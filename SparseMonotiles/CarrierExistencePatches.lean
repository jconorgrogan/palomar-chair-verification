module

public import SparseMonotiles.CarrierHierarchyRefinement
public import SparseMonotiles.CarrierHierarchyExhaustion

@[expose] public section

/-! Explicit finite carrier patches, not an assumed infinite world. Every
operation below acts on the literal registered poses used by the hierarchy. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative)
    (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

/-- Translation by a constant diagonal vector. -/
def move {d : ℕ} (t : ℤ) (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => p.shift i + t

@[simp] theorem move_zero {d : ℕ} (p : Pose d) : move 0 p = p := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [move]

@[simp] theorem move_move {d : ℕ} (s t : ℤ) (p : Pose d) :
    move s (move t p) = move (s + t) p := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [move]
    ring

theorem move_injective {d : ℕ} (t : ℤ) : Function.Injective (move (d := d) t) := by
  intro p q h
  have h' := congrArg (move (-t)) h
  simpa using h'

theorem move_compose {d : ℕ} (t : ℤ) (p q : Pose d) :
    move t (compose p q) = compose (move t p) q := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    cases hn : p.negative i <;> simp [move, compose, Pose.sign, hn] <;> ring

theorem move_central {d : ℕ} (t : ℤ) (p : Pose d) :
    move t (centralChild p) = centralChild (move t p) := by
  rw [← compose_central, move_compose, compose_central]

theorem dilate_move {d : ℕ} (t : ℤ) (p : Pose d) :
    dilatePose (move t p) = move (2*t) (dilatePose p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [move, dilatePose]
    ring

theorem move_occupies {d : ℕ} (t : ℤ) (p : Pose d) (c : Cell d) :
    Occupies (move t p) c ↔ Occupies p (fun i => c i - t) := by
  have he : (move t p).inverseCell c = p.inverseCell (fun i => c i - t) := by
    funext i
    cases hn : p.negative (p.perm.symm i) <;>
      simp [Pose.inverseCell, move, Pose.sign, hn] <;> ring
  simp only [Occupies, he]

theorem move_child {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (t : ℤ)
    {p q : Pose d} (h : q ∈ children σ p) :
    move t q ∈ children σ (move t p) := by
  rcases h with rfl | ⟨a, ha, rfl⟩
  · exact Or.inl (move_central t p)
  · exact Or.inr ⟨a, ha, move_compose t p _⟩

@[simp] theorem move_child_iff {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (t : ℤ) (p q : Pose d) :
    move t q ∈ children σ (move t p) ↔ q ∈ children σ p := by
  constructor
  · intro h
    simpa using move_child σ (-t) h
  · exact move_child σ t

def movedTiles {d : ℕ} (t : ℤ) (S : Set (Pose d)) : Set (Pose d) :=
  {q | ∃ p ∈ S, q = move t p}

@[simp] theorem movedTiles_zero {d : ℕ} (S : Set (Pose d)) : movedTiles 0 S = S := by
  ext p
  simp [movedTiles]

@[simp] theorem movedTiles_move {d : ℕ} (s t : ℤ) (S : Set (Pose d)) :
    movedTiles s (movedTiles t S) = movedTiles (s+t) S := by
  ext q
  constructor
  · rintro ⟨p, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, move_move s t r⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨move t p, ⟨p, hp, rfl⟩, (move_move s t p).symm⟩

theorem movedTiles_mono {d : ℕ} (t : ℤ) {S T : Set (Pose d)} (h : S ⊆ T) :
    movedTiles t S ⊆ movedTiles t T := by
  rintro q ⟨p, hp, rfl⟩
  exact ⟨p, h hp, rfl⟩

theorem refinedTiles_move {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (t : ℤ) (S : Set (Pose d)) :
    refinedTiles σ (movedTiles t S) = movedTiles (2*t) (refinedTiles σ S) := by
  ext q
  constructor
  · rintro ⟨p, ⟨P, hP, rfl⟩, hq⟩
    rw [dilate_move] at hq
    have hchild : move (-(2*t)) q ∈ children σ (dilatePose P) := by
      simpa using move_child σ (-(2*t)) hq
    refine ⟨move (-(2*t)) q, ⟨P, hP, hchild⟩, ?_⟩
    simp
  · rintro ⟨p, ⟨P, hP, hp⟩, rfl⟩
    refine ⟨move t P, ⟨P, hP, rfl⟩, ?_⟩
    rw [dilate_move]
    exact move_child σ (2*t) hp

def stages {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) : ℕ → Set (Pose d) → Set (Pose d)
  | 0, S => S
  | n+1, S => refinedTiles σ (stages σ n S)

theorem stages_mono {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ)
    {S T : Set (Pose d)} (h : S ⊆ T) : stages σ n S ⊆ stages σ n T := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rintro q ⟨p, hp, hq⟩
      exact ⟨p, ih hp, hq⟩

theorem stages_add {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n k : ℕ)
    (S : Set (Pose d)) : stages σ (n+k) S = stages σ n (stages σ k S) := by
  induction n with
  | zero => simp only [Nat.zero_add, stages]
  | succ n ih => simpa only [Nat.succ_add, stages, ih]

theorem stages_move {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ)
    (t : ℤ) (S : Set (Pose d)) :
    stages σ n (movedTiles t S) = movedTiles (2^n*t) (stages σ n S) := by
  induction n with
  | zero => simp [stages]
  | succ n ih =>
      simp only [stages, ih, refinedTiles_move, pow_succ]
      congr 1
      ring

def Disjoint {d : ℕ} (S : Set (Pose d)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ c, Occupies p c → Occupies q c → p = q

theorem stages_disjoint {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ)
    {S : Set (Pose d)} (h : Disjoint S) : Disjoint (stages σ n S) := by
  induction n with
  | zero => exact h
  | succ n ih => exact refinedTiles_disjoint σ _ ih

theorem movedTiles_disjoint {d : ℕ} (t : ℤ) {S : Set (Pose d)}
    (h : Disjoint S) : Disjoint (movedTiles t S) := by
  rintro p ⟨P, hP, rfl⟩ q ⟨Q, hQ, rfl⟩ c hp hq
  exact congrArg (move t) (h P hP Q hQ _ ((move_occupies t P c).mp hp)
    ((move_occupies t Q c).mp hq))

/-- Cell support of the literal scale-2^n chair. -/
def ScaledCell {d : ℕ} (n : ℕ) (c : Cell d) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i < 2*2^n) ∧ ∃ i, c i < 2^n

@[simp] theorem scaledCell_zero {d : ℕ} (c : Cell d) :
    ScaledCell 0 c ↔ IsChairCell c := by
  simp only [ScaledCell, IsChairCell, pow_zero, mul_one]
  constructor
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by have hj := hb i; omega⟩
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by omega⟩

theorem scaledCell_half {d : ℕ} (n : ℕ) (c : Cell d) :
    ScaledCell n (halfCell c) ↔ ScaledCell (n+1) c := by
  simp only [ScaledCell, halfCell, pow_succ]
  constructor
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by omega⟩
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by omega⟩

def patch {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ) : Set (Pose d) :=
  stages σ n {rootPose d}

theorem patch_disjoint {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ) :
    Disjoint (patch σ n) := by
  apply stages_disjoint
  intro p hp q hq c _ _
  exact hp.trans hq.symm

theorem patch_support {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (n : ℕ) (c : Cell d) :
    (∃ q ∈ patch σ n, Occupies q c) ↔ ScaledCell n c := by
  induction n generalizing c with
  | zero =>
      rw [scaledCell_zero]
      change (∃ q ∈ ({rootPose d} : Set (Pose d)), Occupies q c) ↔ _
      simp only [Set.mem_singleton_iff, exists_eq_left]
      unfold Occupies
      have hc : (rootPose d).inverseCell c = c := by
        funext i
        simp [Pose.inverseCell, rootPose, Pose.sign]
      rw [hc]
  | succ n ih =>
      change (∃ q ∈ refinedTiles σ (patch σ n), Occupies q c) ↔ _
      rw [refinedTiles_support, ih, scaledCell_half]

#print axioms patch_support
#print axioms patch_disjoint
#print axioms stages_move
end SparseMonotiles.CarrierHierarchy.Existence
