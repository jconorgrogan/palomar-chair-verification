module

public import SparseMonotiles.BoundaryInventory
public import SparseMonotiles.CanonicalRidgeRank

@[expose] public section

/-! Finite active-plane covers of actual Boolean material boundaries. These
lemmas retain the index of each equation and work before any generic-ridge
selection. They are intended for the key-apex recognition step. -/
namespace SparseMonotiles
open Set Filter
open scoped Topology Classical

/-- Every boundary point of a closed finite Boolean halfspace expression lies
on one of its actual defining zero planes. -/
theorem frontier_closed_truth_region_subset_zero
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (Φ : (ι → Prop) → Prop) :
    frontier (closure {x | Φ (fun i => 0 ≤ f i x)}) ⊆ {x | ∃ i, f i x=0} := by
  classical
  intro x hx
  by_contra hnot
  have hn : ∀ i, f i x ≠ 0 := fun i h => hnot ⟨i,h⟩
  have hlocal := localSetEq_freeze_truthFunction f x (fun i => (hf i).continuousAt) Φ
  have hc : {y | Φ (frozenHalfspacePredicates f x y)} =
      (if Φ (fun i => 0 ≤ f i x) then univ else ∅) := by
    ext y
    have he : frozenHalfspacePredicates f x y = (fun i => 0 ≤ f i x) := by
      funext i
      simp only [frozenHalfspacePredicates,if_neg (hn i)]
    change Φ (frozenHalfspacePredicates f x y) ↔ _
    rw [he]
    by_cases h : Φ (fun i => 0 ≤ f i x) <;> simp [h]
  have h := hlocal.closure.frontier.mem_iff.mp hx
  rw [hc] at h
  by_cases hΦ : Φ (fun i => 0 ≤ f i x) <;> simpa [hΦ] using h

/-- Near the chosen point only its already-active zero planes are needed. -/
theorem eventually_frontier_closed_truth_region_active
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (Φ : (ι → Prop) → Prop) (p : X) :
    ∀ᶠ x in 𝓝 p, x ∈ frontier (closure {x | Φ (fun i => 0 ≤ f i x)}) →
      ∃ i, f i p=0 ∧ f i x=0 := by
  filter_upwards [eventually_inactive_signs f p (fun i => (hf i).continuousAt)] with x hx hfront
  obtain ⟨i,hi⟩ := frontier_closed_truth_region_subset_zero f hf Φ hfront
  refine ⟨i,?_,hi⟩
  by_contra h
  rcases hx i h with ⟨hpos,_⟩ | ⟨hneg,_⟩ <;> linarith

/-- Signed atoms allow both orientations while retaining only the underlying
zero-plane index in the boundary conclusion. -/
noncomputable def signedFields {X ι : Type*} (f : ι → X → ℝ) : (ι × Bool) → X → ℝ :=
  fun j x => if j.2 then f j.1 x else -f j.1 x

theorem eventually_frontier_signed_truth_region_active
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (Φ : ((ι × Bool) → Prop) → Prop) (p : X) :
    ∀ᶠ x in 𝓝 p, x ∈ frontier (closure {x | Φ (fun j => 0 ≤ signedFields f j x)}) →
      ∃ i, f i p=0 ∧ f i x=0 := by
  have hcont (j : ι × Bool) : Continuous (signedFields f j) := by
    change Continuous (fun x => if j.2 then f j.1 x else -f j.1 x)
    cases hb : j.2
    · simp only [Bool.false_eq_true,if_false]
      exact (hf j.1).neg
    · simp only [if_true]
      exact hf j.1
  filter_upwards [eventually_frontier_closed_truth_region_active (signedFields f) hcont Φ p] with x hx hfront
  obtain ⟨⟨i,b⟩,hp,hx⟩ := hx hfront
  cases b <;> simp only [signedFields,Bool.false_eq_true,if_false,if_true,neg_eq_zero] at hp hx <;>
    exact ⟨i,hp,hx⟩

/-- A local material model transfers its active-plane boundary cover to the
actual physical set, including the closure used for dents. -/
theorem LocalSetEq.eventually_frontier_signed_active
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (Φ : ((ι × Bool) → Prop) → Prop) {p : X} {T : Set X}
    (h : LocalSetEq p T (_root_.closure {x | Φ (fun j => 0 ≤ signedFields f j x)})) :
    ∀ᶠ x in 𝓝 p, x ∈ _root_.frontier T → ∃ i, f i p=0 ∧ f i x=0 := by
  filter_upwards [h.frontier,eventually_frontier_signed_truth_region_active f hf Φ p] with x hx hc hfront
  exact hc (hx.mp hfront)

/-- A finite family of proper codimension-one affine planes covers the actual
boundary locally, and every retained plane passes through the base point. -/
def HasLocalBoundaryPlaneCover {d : ℕ} (T : Set (Point d)) (p : Point d) (bound : ℕ) : Prop :=
  ∃ planes : Finset (AffineSubspace ℝ (Point d)), planes.card ≤ bound ∧
    (∀ P ∈ planes, p ∈ P ∧ Module.finrank ℝ P.direction+1=d ∧ P ≠ ⊤) ∧
    ∀ᶠ x in 𝓝 p, x ∈ frontier T → ∃ P ∈ planes, x ∈ P

/-- Convert a finite active equation family to genuine codimension-one planes.
Nonzero normals and the actual equation/plane equivalence are explicit. -/
theorem localBoundaryPlaneCover_of_finite_active_fields {d : ℕ} {ι : Type*} [Fintype ι]
    {T : Set (Point d)} (p : Point d) (bound : ℕ) (f : ι → Point d → ℝ)
    (N : ι → Point d) (hN : ∀ i, N i ≠ 0)
    (hcount : (Finset.univ.filter (fun i => f i p=0)).card ≤ bound)
    (hform : ∀ i, f i p=0 → ∀ x, f i x=0 ↔
      inner (𝕜 := ℝ) (N i) x = inner (𝕜 := ℝ) (N i) p)
    (hcover : ∀ᶠ x in 𝓝 p, x ∈ frontier T → ∃ i, f i p=0 ∧ f i x=0) :
    HasLocalBoundaryPlaneCover T p bound := by
  classical
  let active := Finset.univ.filter (fun i => f i p=0)
  let plane := fun i => normalAffineIntersection (fun _ : Fin 1 => N i) p
  refine ⟨active.image plane,(Finset.card_image_le).trans hcount,?_,?_⟩
  · intro P hP
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hP
    have hdim : Module.finrank ℝ (plane i).direction+1=d := by
      simpa only [Fintype.card_fin] using normalAffineIntersection_codimension
        (fun _ : Fin 1 => N i) (linearIndependent_unique_iff.mpr (hN i)) p
    refine ⟨?_,hdim,?_⟩
    · dsimp only [plane]
      rw [mem_normalAffineIntersection_iff]
      exact fun _ => rfl
    · intro htop
      have hin : N i+p ∈ plane i := by rw [htop]; trivial
      have hz := (mem_normalAffineIntersection_iff (fun _ : Fin 1 => N i) p (N i+p)).mp hin 0
      rw [inner_add_right] at hz
      linarith [real_inner_self_pos.mpr (hN i)]
  · filter_upwards [hcover] with x hx hfront
    obtain ⟨i,hi,hix⟩ := hx hfront
    refine ⟨plane i,Finset.mem_image.mpr ⟨i,?_,rfl⟩,?_⟩
    · simp [active,hi]
    · dsimp only [plane]
      rw [mem_normalAffineIntersection_iff]
      exact fun _ => (hform i hi x).mp hix

#print axioms frontier_closed_truth_region_subset_zero
#print axioms eventually_frontier_signed_truth_region_active
#print axioms localBoundaryPlaneCover_of_finite_active_fields
end SparseMonotiles
