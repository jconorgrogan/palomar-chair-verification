module

public import SparseMonotiles.CarrierExistencePatches

@[expose] public section

/-! The alternating empty/central ancestors are nested as actual leaf-pose
sets, and their literal occupied cells exhaust the integer lattice. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative)
    (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem empty_outer {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) :
    outerPose (fun _ : Fin d => false) (σ (fun _ => false)) = rootPose d := by
  apply pose_ext
  · exact he
  · rfl
  · funext i
    simp [outerPose, rootPose, bit]

theorem central_in_patch_one {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) :
    centralPose d ∈ patch σ 1 := by
  refine ⟨rootPose d, rfl, Or.inl ?_⟩
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [centralPose, centralChild, dilatePose, rootPose, Pose.sign]

/-- In the two-level supertile, the empty child of its central child is the
same marked frame translated by 2 in every coordinate. -/
theorem seed_in_patch_two {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) :
    move 2 (rootPose d) ∈ patch σ 2 := by
  refine ⟨centralPose d, central_in_patch_one σ, Or.inr ⟨fun _ => false, ?_, ?_⟩⟩
  · exact ⟨⟨0, hd⟩, rfl⟩
  · rw [empty_outer σ he, compose_root_right]
    apply pose_ext
    · rfl
    · rfl
    · funext i
      norm_num [move, rootPose, dilatePose, centralPose]

theorem patch_two_embed {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) (n : ℕ) :
    movedTiles (2^n*2) (patch σ n) ⊆ patch σ (n+2) := by
  have hs : movedTiles 2 ({rootPose d} : Set (Pose d)) ⊆ patch σ 2 := by
    rintro q ⟨p, hp, rfl⟩
    subst p
    exact seed_in_patch_two hd σ he
  have hm := stages_mono σ n hs
  rw [stages_move] at hm
  simpa only [patch, stages_add] using hm

def ancestorPatch {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (m : ℕ) : Set (Pose d) :=
  movedTiles (-ancestorOffset m) (patch σ (2*m))

/-- Previously placed unit chairs remain exactly the same registered poses. -/
theorem ancestorPatch_step {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) (m : ℕ) :
    ancestorPatch σ m ⊆ ancestorPatch σ (m+1) := by
  have hm := movedTiles_mono (-ancestorOffset (m+1)) (patch_two_embed hd σ he (2*m))
  rw [movedTiles_move] at hm
  have hp : (2 : ℤ)^(2*m) = 4^m := by rw [pow_mul]; norm_num
  have ha : -ancestorOffset (m+1) + 2^(2*m)*2 = -ancestorOffset m := by
    rw [ancestorOffset, hp]
    ring
  rw [ha] at hm
  simpa only [ancestorPatch, Nat.mul_add, Nat.mul_one] using hm

theorem ancestorPatch_mono {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) : Monotone (ancestorPatch σ) :=
  monotone_nat_of_le_succ (ancestorPatch_step hd σ he)

theorem ancestorPatch_disjoint {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (m : ℕ) :
    Disjoint (ancestorPatch σ m) := movedTiles_disjoint _ (patch_disjoint σ _)

/-- Exact support identity binds the finite leaf construction to the proved
alternating-ancestor boxes, including the genuinely omitted upper corner. -/
theorem ancestorPatch_support {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (m : ℕ) (c : Cell d) :
    (∃ q ∈ ancestorPatch σ m, Occupies q c) ↔ AncestorCell m c := by
  have hp : (2 : ℤ)^(2*m) = 4^m := by rw [pow_mul]; norm_num
  have hs : (∃ q ∈ ancestorPatch σ m, Occupies q c) ↔
      ∃ p ∈ patch σ (2*m), Occupies p (fun i => c i + ancestorOffset m) := by
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, hq⟩
      exact ⟨p, hp, by simpa using (move_occupies (-ancestorOffset m) p c).mp hq⟩
    · rintro ⟨p, hp, hpc⟩
      refine ⟨move (-ancestorOffset m) p, ⟨p, hp, rfl⟩, ?_⟩
      apply (move_occupies _ _ _).mpr
      simpa using hpc
  rw [hs, patch_support]
  simp only [ScaledCell, AncestorCell, hp]
  constructor
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by omega⟩
  · rintro ⟨hb, i, hi⟩
    exact ⟨fun j => by have hj := hb j; omega, i, by omega⟩

theorem ancestorPatch_exhaustive {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d)) (c : Cell d) :
    ∃ m, ∃ p ∈ ancestorPatch σ m, Occupies p c := by
  obtain ⟨m, hm⟩ := ancestorCell_exhaustive hd c
  exact ⟨m, (ancestorPatch_support σ m c).mpr hm⟩

/-- All leaves in some finite alternating ancestor. -/
def limitTiles {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) : Set (Pose d) :=
  {p | ∃ m, p ∈ ancestorPatch σ m}

/-- A full registered chair tiling constructed from explicit nested finite
substitutions. Neither existence nor exhaustion is an input. -/
def world {d : ℕ} (hd : 0 < d) (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) : RegisteredWorld d where
  tiles := limitTiles σ
  covers := by
    intro c
    obtain ⟨m, p, hp, hpc⟩ := ancestorPatch_exhaustive hd σ c
    exact ⟨p, ⟨m, hp⟩, hpc⟩
  disjoint := by
    rintro p ⟨m, hp⟩ q ⟨n, hq⟩ c hpc hqc
    exact ancestorPatch_disjoint σ (max m n) p
      (ancestorPatch_mono hd σ he (le_max_left m n) hp) q
      (ancestorPatch_mono hd σ he (le_max_right m n) hq) c hpc hqc

#print axioms seed_in_patch_two
#print axioms ancestorPatch_step
#print axioms ancestorPatch_support
#print axioms world
end SparseMonotiles.CarrierHierarchy.Existence
