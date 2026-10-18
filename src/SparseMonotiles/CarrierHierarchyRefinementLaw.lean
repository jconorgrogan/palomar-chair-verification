module

public import SparseMonotiles.CarrierHierarchyRefinement
public import SparseMonotiles.CarrierHierarchyCoarseChecker

@[expose] public section

/-! Derive full-world forward legality from explicit finite sibling and
cross-parent child rules. These rules are the next independent certificate
obligations, not a supplied legal-refinement or infinite-tiling theorem. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem dilatePose_compose {d : ℕ} (p q : Pose d) :
    dilatePose (compose p q) = compose (dilatePose p) (dilatePose q) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    cases h : p.negative i <;> simp [dilatePose, compose, Pose.sign, h] <;> ring

@[simp] theorem dilatePose_root {d : ℕ} : dilatePose (rootPose d) = rootPose d := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [dilatePose, rootPose]

theorem dilatePose_inverse {d : ℕ} (p : Pose d) :
    dilatePose (inversePose p) = inversePose (dilatePose p) := by
  apply compose_left_injective (dilatePose p)
  rw [← dilatePose_compose, compose_inversePose, dilatePose_root, compose_inversePose]

theorem dilatePose_normalize {d : ℕ} (p q : Pose d) :
    dilatePose (normalize p q) = normalize (dilatePose p) (dilatePose q) := by
  simp only [normalize, dilatePose_compose, dilatePose_inverse]

theorem CellContact.remove_common_left {d : ℕ} (P : Pose d) {a b : Pose d}
    (h : CellContact (compose P a) (compose P b)) : CellContact a b := by
  obtain ⟨c, e, hc, he, hadj⟩ := h
  refine ⟨P.inverseCell c, P.inverseCell e, ?_, ?_, ?_⟩
  · apply (occupies_compose_cell P a _).mp
    simpa only [Pose.cell_inverseCell] using hc
  · apply (occupies_compose_cell P b _).mp
    simpa only [Pose.cell_inverseCell] using he
  · simpa only [inversePose_cell] using adjacent_cell_image (inversePose P) hadj

theorem AdjacentCells.half_eq_or_adjacent {d : ℕ} {c e : Cell d} (h : AdjacentCells c e) :
    halfCell c = halfCell e ∨ AdjacentCells (halfCell c) (halfCell e) := by
  obtain ⟨j, hj, hij⟩ := h
  by_cases heq : halfCell e j = halfCell c j
  · left
    funext i
    by_cases hi : i = j
    · subst i
      exact heq.symm
    · simp only [halfCell, hij i hi]
  · right
    refine ⟨j, ?_, ?_⟩
    · simp only [halfCell] at heq ⊢
      rcases hj with hj | hj <;> omega
    · intro i hi
      simp only [halfCell, hij i hi]

/-- A fine cross-parent face contact descends to an actual coarse face; the
same-block alternative is excluded by true coarse cell nonoverlap. -/
theorem refined_parent_contact {d : ℕ} (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c, Occupies p c → Occupies q c → p = q)
    (σ : Bits d → Equiv.Perm (Fin d)) {P Q s t : Pose d}
    (hP : P ∈ tiles) (hQ : Q ∈ tiles) (hne : P ≠ Q)
    (hs : s ∈ children σ (dilatePose P)) (ht : t ∈ children σ (dilatePose Q))
    (hcontact : CellContact s t) : CellContact P Q := by
  obtain ⟨c, e, hc, he, hadj⟩ := hcontact
  have hPc := (dilated_parent_occupies P c).mp
    ((parent_support_dissection σ _ c).mpr ⟨s, hs, hc⟩)
  have hQe := (dilated_parent_occupies Q e).mp
    ((parent_support_dissection σ _ e).mpr ⟨t, ht, he⟩)
  rcases hadj.half_eq_or_adjacent with heq | ha
  · rw [heq] at hPc
    exact False.elim (hne (disjoint P hP Q hQ _ hPc hQe))
  · exact ⟨_, _, hPc, hQe, ha⟩

structure ForwardRules {d : ℕ} (C : Finset (Pose d)) (L : Set (Pose d)) : Prop where
  sibling : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → CellContact a b → normalize a b ∈ L
  cross : ∀ k ∈ L, ∀ a ∈ C, ∀ b ∈ C,
    CellContact a (compose (dilatePose k) b) → normalize a (compose (dilatePose k) b) ∈ L

/-- Full legality of the actual refined world follows from finite canonical
rules, with coarse parent contact derived rather than assumed. -/
def PatchLegal {d : ℕ} (tiles : Set (Pose d)) (L : Set (Pose d)) : Prop :=
  ∀ p ∈ tiles, ∀ q ∈ tiles, p ≠ q → CellContact p q → normalize p q ∈ L

theorem refinedTiles_legal {d : ℕ}
    (σ : Bits d → Equiv.Perm (Fin d)) (C : Finset (Pose d)) (L : Set (Pose d))
    (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c, Occupies p c → Occupies q c → p = q)
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) (hl : PatchLegal tiles L) :
    PatchLegal (refinedTiles σ tiles) L := by
  rintro s ⟨P, hP, hs⟩ t ⟨Q, hQ, ht⟩ hne hcontact
  obtain ⟨a, ha, rfl⟩ := canonical_child_form hC (dilatePose P) hs
  obtain ⟨b, hb, rfl⟩ := canonical_child_form hC (dilatePose Q) ht
  by_cases heq : P = Q
  · subst Q
    rw [normalize_common_left]
    have hab : a ≠ b := by intro h; subst b; exact hne rfl
    exact rules.sibling a ha b hb hab (hcontact.remove_common_left (dilatePose P))
  · have hk := hl P hP Q hQ heq (refined_parent_contact tiles disjoint σ hP hQ heq hs ht hcontact)
    rw [normalized_parent_children, ← dilatePose_normalize]
    apply rules.cross _ hk a ha b hb
    apply CellContact.remove_common_left (dilatePose P)
    simpa only [dilatePose_normalize, ← compose_assoc, compose_normalize] using hcontact

theorem RegisteredWorld.refine_legal {d : ℕ} (W : RegisteredWorld d)
    (σ : Bits d → Equiv.Perm (Fin d)) (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) (hl : W.Legal L) :
    (W.refine σ).Legal L :=
  refinedTiles_legal σ C L W.tiles W.disjoint hC rules hl

#print axioms refined_parent_contact
#print axioms refinedTiles_legal
#print axioms RegisteredWorld.refine_legal
end SparseMonotiles.CarrierHierarchy
