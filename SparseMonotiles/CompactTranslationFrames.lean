module

import all Mathlib.Basic.Real.Basic
public import SparseMonotiles.Model
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Translation-equivariant representatives for compact physical copies

Coordinatewise minima define a translation-equivariant anchor. Normalizing a
copy by that anchor removes every translation, so one choice per normalized
shape gives representatives equivariant under all translations simultaneously.
No freeness, orbit representative, or self-symmetry hypothesis is needed.
-/
namespace SparseMonotiles
open Set

noncomputable def translationIsometry {d : ℕ} (v : Point d) : Point d ≃ᵢ Point d :=
  IsometryEquiv.vaddConst v

@[simp] theorem translationIsometry_apply {d : ℕ} (v x : Point d) :
    translationIsometry v x = x + v := rfl

/-- Physical copies, independently of any chosen tiling. -/
abbrev PhysicalCopy {d : ℕ} (T : Set (Point d)) :=
  {A : Set (Point d) // ∃ g : Point d ≃ᵢ Point d, A = g '' T}

noncomputable def copyRepresentative {d : ℕ} {T : Set (Point d)} (A : PhysicalCopy T) :
    Point d ≃ᵢ Point d := Classical.choose A.property

theorem copyRepresentative_image {d : ℕ} {T : Set (Point d)} (A : PhysicalCopy T) :
    copyRepresentative A '' T = (A : Set (Point d)) := (Classical.choose_spec A.property).symm

noncomputable def translatedCopy {d : ℕ} {T : Set (Point d)}
    (v : Point d) (A : PhysicalCopy T) : PhysicalCopy T :=
  ⟨translate v A, ⟨(copyRepresentative A).trans (translationIsometry v), by
    rw [translate, ← copyRepresentative_image A, Set.image_image]
    rfl⟩⟩

theorem translatedCopy_add {d : ℕ} {T : Set (Point d)}
    (u v : Point d) (A : PhysicalCopy T) :
    translatedCopy u (translatedCopy v A) = translatedCopy (v+u) A := by
  apply Subtype.ext
  change (fun x => x+u) '' ((fun x => x+v) '' (A : Set (Point d))) =
    (fun x => x+(v+u)) '' A
  rw [Set.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply,add_assoc]

@[simp] theorem translatedCopy_zero {d : ℕ} {T : Set (Point d)} (A : PhysicalCopy T) :
    translatedCopy 0 A = A := by
  apply Subtype.ext
  change (fun x : Point d => x+0) '' (A : Set (Point d)) = A
  simp

theorem physicalCopy_isCompact {d : ℕ} {T : Set (Point d)}
    (hT : IsCompact T) (A : PhysicalCopy T) : IsCompact (A : Set (Point d)) := by
  rw [← copyRepresentative_image A]
  exact hT.image (copyRepresentative A).continuous

theorem physicalCopy_nonempty {d : ℕ} {T : Set (Point d)}
    (hT : T.Nonempty) (A : PhysicalCopy T) : (A : Set (Point d)).Nonempty := by
  rw [← copyRepresentative_image A]
  exact hT.image _

noncomputable def copyMinimumPoint {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (i : Fin d) : Point d :=
  Classical.choose ((physicalCopy_isCompact hc A).exists_isMinOn
    (physicalCopy_nonempty hn A) (EuclideanSpace.proj i).continuous.continuousOn)

theorem copyMinimumPoint_spec {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (i : Fin d) :
    copyMinimumPoint hc hn A i ∈ (A : Set (Point d)) ∧
    ∀ x ∈ (A : Set (Point d)), copyMinimumPoint hc hn A i i ≤ x i :=
  Classical.choose_spec ((physicalCopy_isCompact hc A).exists_isMinOn
    (physicalCopy_nonempty hn A) (EuclideanSpace.proj i).continuous.continuousOn)

noncomputable def copyAnchor {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => copyMinimumPoint hc hn A i i)

theorem copyAnchor_le {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T)
    {x : Point d} (hx : x ∈ (A : Set (Point d))) (i : Fin d) : copyAnchor hc hn A i ≤ x i :=
  (copyMinimumPoint_spec hc hn A i).2 x hx

theorem copyAnchor_attained {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (i : Fin d) :
    ∃ x ∈ (A : Set (Point d)), x i = copyAnchor hc hn A i :=
  ⟨copyMinimumPoint hc hn A i,(copyMinimumPoint_spec hc hn A i).1,rfl⟩

/-- The anchor shifts by exactly the physical translation. -/
theorem copyAnchor_translate {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (v : Point d) :
    copyAnchor hc hn (translatedCopy v A) = copyAnchor hc hn A + v := by
  ext i
  apply le_antisymm
  · obtain ⟨x,hx,hxi⟩ := copyAnchor_attained hc hn A i
    have h := copyAnchor_le hc hn (translatedCopy v A)
      (show x+v ∈ (translatedCopy v A : Set (Point d)) from ⟨x,hx,rfl⟩) i
    change copyAnchor hc hn (translatedCopy v A) i ≤ x i+v i at h
    change copyAnchor hc hn (translatedCopy v A) i ≤ copyAnchor hc hn A i + v i
    rw [← hxi]
    exact h
  · obtain ⟨y,hy,hyi⟩ := copyAnchor_attained hc hn (translatedCopy v A) i
    rcases hy with ⟨x,hx,rfl⟩
    have h := copyAnchor_le hc hn A hx i
    change x i+v i = copyAnchor hc hn (translatedCopy v A) i at hyi
    change copyAnchor hc hn A i+v i ≤ copyAnchor hc hn (translatedCopy v A) i
    linarith

noncomputable def normalizedCopy {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) : PhysicalCopy T :=
  translatedCopy (-copyAnchor hc hn A) A

/-- Normalized physical shapes are exactly unchanged under translation. -/
theorem normalizedCopy_translate {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (v : Point d) :
    normalizedCopy hc hn (translatedCopy v A) = normalizedCopy hc hn A := by
  unfold normalizedCopy
  rw [copyAnchor_translate,translatedCopy_add]
  congr 1
  abel

noncomputable def translationEquivariantFrame {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) : Point d ≃ᵢ Point d :=
  (copyRepresentative (normalizedCopy hc hn A)).trans (translationIsometry (copyAnchor hc hn A))

theorem translationEquivariantFrame_image {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) :
    translationEquivariantFrame hc hn A '' T = (A : Set (Point d)) := by
  change (fun x => copyRepresentative (normalizedCopy hc hn A) x + copyAnchor hc hn A) '' T = _
  rw [← Set.image_image (fun x => x+copyAnchor hc hn A)
    (copyRepresentative (normalizedCopy hc hn A)) T, copyRepresentative_image]
  change (translatedCopy (copyAnchor hc hn A) (translatedCopy (-copyAnchor hc hn A) A) :
    Set (Point d)) = A
  rw [translatedCopy_add,neg_add_cancel,translatedCopy_zero]

/-- Representatives commute with every physical translation, not just one
selected period. -/
theorem translationEquivariantFrame_translate {d : ℕ} {T : Set (Point d)}
    (hc : IsCompact T) (hn : T.Nonempty) (A : PhysicalCopy T) (v : Point d) :
    translationEquivariantFrame hc hn (translatedCopy v A) =
      (translationEquivariantFrame hc hn A).trans (translationIsometry v) := by
  apply IsometryEquiv.ext
  intro x
  change copyRepresentative (normalizedCopy hc hn (translatedCopy v A)) x +
      copyAnchor hc hn (translatedCopy v A) =
    (copyRepresentative (normalizedCopy hc hn A) x + copyAnchor hc hn A) + v
  rw [normalizedCopy_translate,copyAnchor_translate,add_assoc]

/-- A compact-body physical tiling admits representatives equivariant under
all of its periods simultaneously. No registration premise is used here. -/
theorem IsTiling.exists_translation_equivariant_representatives {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hc : IsCompact T) :
    ∃ g : tiles → Point d ≃ᵢ Point d,
      (∀ A : tiles, (A : Set (Point d)) = g A '' T) ∧
      ∀ v, ∀ hp : IsPeriod tiles v, ∀ A : tiles,
        g ⟨translate v A,(hp A).mp A.property⟩ = (g A).trans (translationIsometry v) := by
  have hn : T.Nonempty := by
    obtain ⟨A,hA,h0⟩ := ht.2.1 (0 : Point d)
    obtain ⟨e,he⟩ := ht.1 A hA
    rw [he] at h0
    obtain ⟨x,hx,_⟩ := h0
    exact ⟨x,hx⟩
  let g : tiles → Point d ≃ᵢ Point d := fun A =>
    translationEquivariantFrame hc hn ⟨A,ht.1 A A.property⟩
  refine ⟨g, ?_, ?_⟩
  · intro A
    exact (translationEquivariantFrame_image hc hn ⟨A,ht.1 A A.property⟩).symm
  · intro v hp A
    exact translationEquivariantFrame_translate hc hn ⟨A,ht.1 A A.property⟩ v

#print axioms copyAnchor_translate
#print axioms translationEquivariantFrame_translate
#print axioms IsTiling.exists_translation_equivariant_representatives
end SparseMonotiles
