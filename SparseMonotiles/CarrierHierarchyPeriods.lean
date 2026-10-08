module

public import SparseMonotiles.CarrierHierarchyCoarseWorldLaw
public import SparseMonotiles.PeriodEndpoint

@[expose] public section

/-!
Translation periods of registered worlds pass to the actual parent partition,
become even, and halve under coarsening. Iteration is justified by the concrete
finite-certificate premises that preserve the contact language; no hierarchy or
period divisibility is assumed as an input.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

def translatePose {d : ℕ} (v : Cell d) (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => p.shift i + v i

@[simp] theorem translatePose_neg {d : ℕ} (v : Cell d) (p : Pose d) :
    translatePose (-v) (translatePose v p) = p := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [translatePose]

@[simp] theorem translatePose_add_neg {d : ℕ} (v : Cell d) (p : Pose d) :
    translatePose v (translatePose (-v) p) = p := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [translatePose]

theorem translate_compose {d : ℕ} (v : Cell d) (p q : Pose d) :
    translatePose v (compose p q) = compose (translatePose v p) q := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    change p.sign i * q.shift (p.perm i) + p.shift i + v i =
      p.sign i * q.shift (p.perm i) + (p.shift i + v i)
    ring

theorem centralParent_translate {d : ℕ} (v : Cell d) (p : Pose d) :
    centralParent (translatePose v p) = translatePose v (centralParent p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    change p.shift i + v i - p.sign i = (p.shift i - p.sign i) + v i
    ring

theorem centralChild_translate {d : ℕ} (v : Cell d) (p : Pose d) :
    centralChild (translatePose v p) = translatePose v (centralChild p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    change p.shift i + v i + p.sign i = (p.shift i + p.sign i) + v i
    ring

theorem GaugeRel.translate {d : ℕ} {r : Equiv.Perm (Fin d)} {p q : Pose d}
    (h : GaugeRel r p q) (v : Cell d) : GaugeRel r (translatePose v p) (translatePose v q) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

def RegisteredWorld.IsPeriod {d : ℕ} (W : RegisteredWorld d) (v : Cell d) : Prop :=
  ∀ p, p ∈ W.tiles ↔ translatePose v p ∈ W.tiles

theorem RegisteredWorld.IsPeriod.neg {d : ℕ} {W : RegisteredWorld d} {v : Cell d}
    (h : W.IsPeriod v) : W.IsPeriod (-v) := by
  intro p
  have hp := h (translatePose (-v) p)
  simpa only [translatePose_add_neg] using hp.symm

theorem CompleteParent.translate {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} {W : RegisteredWorld d} {p : Pose d}
    (hp : CompleteParent σ r W.tiles p) {v : Cell d} (hv : W.IsPeriod v) :
    CompleteParent σ r W.tiles (translatePose v p) := by
  intro q hq
  have hbase : ∃ s ∈ children σ p, q = translatePose v s := by
    rcases hq with rfl | ⟨a, ha, rfl⟩
    · exact ⟨centralChild p, Or.inl rfl, centralChild_translate v p⟩
    · exact ⟨compose p (outerPose a (σ a)), Or.inr ⟨a, ha, rfl⟩,
        (translate_compose v p _).symm⟩
  obtain ⟨s, hs, rfl⟩ := hbase
  obtain ⟨t, ht, hg⟩ := hp s hs
  exact ⟨translatePose v t, (hv t).mp ht, hg.translate v⟩

theorem RegisteredWorld.period_even {d : ℕ} (W : RegisteredWorld d) (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    {v : Cell d} (hv : W.IsPeriod v) : ∀ i, v i % 2 = 0 := by
  obtain ⟨p, hp⟩ := W.has_complete_parent hd hL hl
  have h := W.all_parents_even hd hr he hL hl p hp (translatePose v p) (hp.translate hv)
  intro i
  have hi := h i
  change (p.shift i + v i - p.shift i) % 2 = 0 at hi
  omega

def halfVector {d : ℕ} (v : Cell d) : Cell d := fun i => v i / 2

private theorem halfVector_neg {d : ℕ} (v : Cell d) (h : ∀ i, v i % 2 = 0) :
    halfVector (-v) = -halfVector v := by
  funext i
  have hi := h i
  simp only [halfVector, Pi.neg_apply]
  omega

private theorem coarse_translate {d : ℕ} (origin : Cell d) (p : Pose d)
    (v : Cell d) (hv : ∀ i, v i % 2 = 0) :
    coarsePose origin (translatePose v p) = translatePose (halfVector v) (coarsePose origin p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    have hi := hv i
    change (p.shift i + v i - origin i) / 2 = (p.shift i - origin i) / 2 + v i / 2
    omega

private theorem coarse_period_forward {d : ℕ} (W : RegisteredWorld d) (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p₀ : Pose d) (hp₀ : CompleteParent σ r W.tiles p₀)
    {v : Cell d} (hv : W.IsPeriod v) (hEven : ∀ i, v i % 2 = 0) :
    ∀ p ∈ (W.coarsen hd hr he hL hl p₀ hp₀).tiles,
      translatePose (halfVector v) p ∈ (W.coarsen hd hr he hL hl p₀ hp₀).tiles := by
  rintro p ⟨t, ht, hpt, rfl⟩
  refine ⟨translatePose v t, (hv t).mp ht, ?_, ?_⟩
  · rw [centralParent_translate]
    exact hpt.translate hv
  · rw [centralParent_translate, coarse_translate p₀.shift _ v hEven]

/-- A period of the fine world becomes half that period in the actual coarse world. -/
theorem RegisteredWorld.coarsen_period {d : ℕ} (W : RegisteredWorld d) (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p₀ : Pose d) (hp₀ : CompleteParent σ r W.tiles p₀)
    {v : Cell d} (hv : W.IsPeriod v) :
    (W.coarsen hd hr he hL hl p₀ hp₀).IsPeriod (halfVector v) := by
  have hEven := W.period_even hd hr he hL hl hv
  have hEvenNeg : ∀ i, (-v) i % 2 = 0 := by
    intro i
    have hi := hEven i
    change (-v i) % 2 = 0
    omega
  intro p
  constructor
  · exact coarse_period_forward W hd hr he hL hl p₀ hp₀ hv hEven p
  · intro hp
    have h := coarse_period_forward W hd hr he hL hl p₀ hp₀ hv.neg hEvenNeg _ hp
    rw [halfVector_neg v hEven, translatePose_neg] at h
    exact h

/-- Kernel-derived dyadic period divisibility for every level. The sole finite
input beyond the concrete language/table is its checked aligned coarse rows. -/
theorem registered_period_dyadic {d : ℕ} {ρ : Type} (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : IsCanonicalTable σ C)
    (hGauge : GaugeClosed r L) (hL : ∀ q ∈ L, LocalCatalogFacts σ r q)
    (rows : ρ → CoarseRow d) (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose)
    (covered : ∀ a ∈ C, ∀ b ∈ C, ∀ k ∈ L,
      (∀ j, (parentCandidate a b k).shift j % 2 = 0) →
      ∃ i, parentCandidate a b k = (rows i).pose) :
    ∀ n : ℕ, ∀ W : RegisteredWorld d, W.Legal L → ∀ v, W.IsPeriod v →
      ∀ i, (2 : ℤ)^n ∣ v i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
      intro W hl v hv i
      obtain ⟨p₀, hp₀⟩ := W.has_complete_parent hd hL hl
      let V := W.coarsen hd hr he hL hl p₀ hp₀
      have hV : V.Legal L := W.coarsen_legal hd hr he C L hC hGauge hL hl rows valid covered p₀ hp₀
      have hvV : V.IsPeriod (halfVector v) := W.coarsen_period hd hr he hL hl p₀ hp₀ hv
      obtain ⟨k, hk⟩ := ih V hV (halfVector v) hvV i
      have heven := W.period_even hd hr he hL hl hv i
      have hhalf : v i = 2 * halfVector v i := by simp only [halfVector]; omega
      refine ⟨k, ?_⟩
      rw [hhalf, hk, pow_succ]
      ring

/-- The registered-world aperiodicity endpoint; physical-body registration and
physical-period transport are still separate geometric obligations. -/
theorem registered_period_zero {d : ℕ} {ρ : Type} (hd : 3 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : IsCanonicalTable σ C)
    (hGauge : GaugeClosed r L) (hL : ∀ q ∈ L, LocalCatalogFacts σ r q)
    (rows : ρ → CoarseRow d) (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose)
    (covered : ∀ a ∈ C, ∀ b ∈ C, ∀ k ∈ L,
      (∀ j, (parentCandidate a b k).shift j % 2 = 0) →
      ∃ i, parentCandidate a b k = (rows i).pose)
    (W : RegisteredWorld d) (hl : W.Legal L) (v : Cell d) (hv : W.IsPeriod v) : v = 0 :=
  integer_vector_eq_zero_of_all_dyadic_dvd v
    (fun n => registered_period_dyadic hd hr he C L hC hGauge hL rows valid covered n W hl v hv)

#print axioms CompleteParent.translate
#print axioms RegisteredWorld.period_even
#print axioms RegisteredWorld.coarsen_period
#print axioms registered_period_dyadic
#print axioms registered_period_zero
end SparseMonotiles.CarrierHierarchy
