module
public import CatalogEntryScreen7
@[expose] public section
namespace CompactT7Preparation
open RegisteredPrime

abbrev P7 : Parameters where
  p := 7
  prime := ⟨by decide, by
    intro m hm
    have hle : m ≤ 7 := Nat.le_of_dvd (by decide) hm
    have h : ∀ k : Fin 8, k.val ∣ 7 → k.val = 1 ∨ k.val = 7 := by decide
    exact h ⟨m, by omega⟩ hm⟩
  odd := by decide
  mu := 1
  g := 6
  mu_nonzero := by decide
  mu_square := ⟨1, by decide⟩
  g_nonzero := by decide
  g_nonsquare := by
    rintro ⟨x, hx⟩
    have h : ∀ a : Fin 7, (a.val * a.val) % 7 ≠ 6 % 7 := by decide
    apply h ⟨x % 7, Nat.mod_lt x (by decide)⟩
    exact (Nat.mul_mod x x 7).symm.trans hx

theorem central7_eq : arithmeticChild P7 .central = H0Pose 7 := by
  apply Pose.Same.eq
  refine ⟨?_, fun _ => rfl, fun _ => rfl⟩
  intro i
  apply Fin.ext
  rw [central_index_value]
  change (1 * i.val) % 7 = i.val
  simp only [Nat.one_mul]
  exact Nat.mod_eq_of_lt i.isLt

def incomingToChild (q : Pose 7) : Pose 7 where
  frame := q.frame
  anchor := fun i => q.anchor i + 1

theorem central_relative_incomingToChild (q : Pose 7) :
    (H0Pose 7).relative (incomingToChild q) = q := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i
    simp [Pose.relative, Pose.inv, Pose.comp, H0Pose, identityPose,
      RegisteredFrame.comp, RegisteredFrame.inv, incomingToChild]
  · intro i
    simp [Pose.relative, Pose.inv, Pose.comp, H0Pose, identityPose,
      RegisteredFrame.linear, RegisteredFrame.sign, RegisteredFrame.inv,
      incomingToChild]
    omega

theorem sibling_relative_generated (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    GeneratedContact P ((arithmeticChild P .central).relative
      (arithmeticChild P (.outer A hA))) :=
  ⟨1, arithmeticChild P .central, arithmeticChild P (.outer A hA),
    child_is_descendant P .central, child_is_descendant P (.outer A hA),
    central_outer_face_contact P A hA, Pose.Same.refl _⟩

theorem generated_of_exact_outer_child (q : Pose 7) (hA : Proper q.frame.negative)
    (hchild : arithmeticChild P7 (.outer q.frame.negative hA) = incomingToChild q) :
    GeneratedContact P7 q := by
  have h := sibling_relative_generated P7 q.frame.negative hA
  rwa [central7_eq, hchild, central_relative_incomingToChild] at h

theorem generated_inverse (P : Parameters) (q : Pose P.p)
    (h : GeneratedContact P q) : GeneratedContact P q.inv := by
  obtain ⟨n, a, b, ha, hb, hc, he⟩ := h
  refine ⟨n, b, a, hb, ha, hc.symm, ?_⟩
  rw [← Pose.relative_reverse, he.eq]
  exact Pose.Same.refl _

theorem even_no_incoming (q : Pose 7) (he : ∀ i, q.anchor i % 2 = 0)
    (A : Mask 7) (hin : IncomingSupport q A) : False := by
  have h0 := he ⟨0, by decide⟩
  have hb := congrFun hin.1 ⟨0, by decide⟩
  change q.anchor ⟨0, by decide⟩ - 2 * bit (q.frame.negative ⟨0, by decide⟩) =
    2 * bit (A ⟨0, by decide⟩) - 1 at hb
  omega

theorem atlas_of_even_wall (q : Pose 7) (screen : EntryScreen q)
    (he : ∀ i, q.anchor i % 2 = 0) (wall : WallGeometry q)
    (noOwner : ¬ UnitChairCell (q.inv.cell (fun _ => 1))) :
    ArithmeticAtlasContact P7 q := by
  refine ⟨⟨screen.1, fun _ => wall, ?_, ?_⟩, screen.2.1, ?_⟩
  · intro A hA hs
    exact False.elim (even_no_incoming q he A hs)
  · intro ho
    exact False.elim (noOwner ((occupies_inverse_iff q _).mp ho))
  · exact screen.2.2

#print axioms P7
#print axioms generated_of_exact_outer_child
#print axioms atlas_of_even_wall
end CompactT7Preparation
