module
public import RegisteredPrime.CoarseWorld
@[expose] public section
namespace RegisteredPrime

/-- The floor image of a unit face edge is either one cell or a unit face edge. -/
theorem adjacent_floor_of_ne {p : Nat} (a b : Cell p) (hab : Adjacent a b)
    (hne : floorCell a ≠ floorCell b) : Adjacent (floorCell a) (floorCell b) := by
  obtain ⟨j, hj, ht⟩ := hab
  have hjne : a j / 2 ≠ b j / 2 := by
    intro he
    apply hne
    funext i
    by_cases hij : i = j
    · subst i
      exact he
    · exact congrArg (fun z : Int => z / 2) (ht i hij)
  refine ⟨j, ?_, ?_⟩
  · change a j / 2 = b j / 2 + 1 ∨ b j / 2 = a j / 2 + 1
    omega
  · intro i hij
    exact congrArg (fun z : Int => z / 2) (ht i hij)

/-- A fine face contact across disjoint parents projects to an actual coarse
face contact, not merely a corner/edge incidence. -/
theorem refined_contact_projects (P : Parameters) (q r : Pose P.p)
    (a b : Role P.p) (hd : Disjoint q r)
    (hc : FaceContact (refine P q a) (refine P r b)) : FaceContact q r := by
  obtain ⟨_, x, y, hx, hy, hxy⟩ := hc
  have hqx := refine_occupies_parent P q a x hx
  have hry := refine_occupies_parent P r b y hy
  have hne : floorCell x ≠ floorCell y := by
    intro he
    exact hd (floorCell y) ⟨he ▸ hqx, hry⟩
  exact ⟨hd, floorCell x, floorCell y, hqx, hry, adjacent_floor_of_ne x y hxy hne⟩

theorem finite_descendants_disjoint (P : Parameters) (n : Nat) (root q r : Pose P.p)
    (hq : Descendant P n root q) (hr : Descendant P n root r) (hne : q ≠ r) :
    Disjoint q r := by
  intro c ⟨hqc, hrc⟩
  exact hne (finite_supertile_unique_owner P n root q r hq hr c hqc hrc).eq

/-- The contact induction may separate same-parent siblings from distinct
actual touching parents; no global hierarchy is assumed. -/
theorem finite_refined_contact_parents (P : Parameters) (n : Nat)
    (root q r : Pose P.p) (hq : Descendant P n root q) (hr : Descendant P n root r)
    (a b : Role P.p) (hc : FaceContact (refine P q a) (refine P r b)) :
    q = r ∨ FaceContact q r := by
  by_cases he : q = r
  · exact Or.inl he
  · exact Or.inr (refined_contact_projects P q r a b
      (finite_descendants_disjoint P n root q r hq hr he) hc)

end RegisteredPrime
