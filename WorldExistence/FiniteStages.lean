module
public import RegisteredPrime.CoarseWorld
@[expose] public section
namespace RegisteredPrime.WorldExistence

/-- Scaling changes only the anchor, retaining the whole marked frame. -/
def scalePose {p : Nat} : Nat → Pose p → Pose p
  | 0, q => q
  | n + 1, q => doubleAnchor (scalePose n q)

def sideLength : Nat → Int
  | 0 => 1
  | n + 1 => 2 * sideLength n

@[simp] theorem scalePose_frame {p : Nat} (n : Nat) (q : Pose p) :
    (scalePose n q).frame = q.frame := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [scalePose, doubleAnchor] using ih

@[simp] theorem scalePose_anchor {p : Nat} (n : Nat) (q : Pose p) (i : Fin p) :
    (scalePose n q).anchor i = sideLength n * q.anchor i := by
  induction n with
  | zero => simp [scalePose, sideLength]
  | succ n ih =>
    change 2 * (scalePose n q).anchor i = (2 * sideLength n) * q.anchor i
    rw [ih]
    exact (Int.mul_assoc _ _ _).symm

@[simp] theorem scalePose_identity (p n : Nat) : scalePose n (identityPose p) = identityPose p := by
  apply Pose.Same.eq
  refine ⟨fun i => by simp, fun i => by simp, fun i => by simp [identityPose]⟩

/-- Transport actual finite descendants through a common registered pose. -/
theorem descendant_comp (P : Parameters) (n : Nat) (g root t : Pose P.p)
    (ht : Descendant P n root t) :
    Descendant P n (g.comp root) ((scalePose n g).comp t) := by
  induction n generalizing root t with
  | zero =>
    have he := ht.eq
    subst t
    exact Pose.Same.refl _
  | succ n ih =>
    obtain ⟨u, a, hu, hta⟩ := (descendant_succ_iff P n root t).mp ht
    have hut := ih root u hu
    apply (descendant_succ_iff P n (g.comp root) _).mpr
    refine ⟨(scalePose n g).comp u, a, hut, ?_⟩
    rw [refine_comp, hta.eq]
    exact Pose.Same.refl _

/-- Concatenation of actual substitution paths, with no hierarchy premise. -/
theorem descendant_concat (P : Parameters) (m n : Nat) (root u t : Pose P.p)
    (hu : Descendant P m root u) (ht : Descendant P n u t) :
    Descendant P (m + n) root t := by
  induction m generalizing root with
  | zero =>
    have he := hu.eq
    subst u
    simpa only [Nat.zero_add] using ht
  | succ m ih =>
    obtain ⟨a, ha⟩ := hu
    have h := ih (refine P root a) ha
    simpa only [Nat.succ_add] using
      (show Descendant P ((m + n) + 1) root t from ⟨a, h⟩)

def floorIter {p : Nat} : Nat → Cell p → Cell p
  | 0, c => c
  | n + 1, c => floorIter n (floorCell c)

/-- Exact finite coverage, obtained by successively refining occupied cells. -/
theorem finite_cover (P : Parameters) (n : Nat) (root : Pose P.p) (c : Cell P.p)
    (hc : Occupies root (floorIter n c)) :
    ∃ t, Descendant P n root t ∧ Occupies t c := by
  induction n generalizing c with
  | zero => exact ⟨root, Pose.Same.refl _, hc⟩
  | succ n ih =>
    obtain ⟨u, hu, huc⟩ := ih (floorCell c) hc
    obtain ⟨a, ha⟩ := parent_occupies_refinement P u c huc
    exact ⟨refine P u a, (descendant_succ_iff P n root _).mpr
      ⟨u, a, hu, Pose.Same.refl _⟩, ha⟩

theorem sideLength_pos (n : Nat) : 0 < sideLength n := by
  induction n with
  | zero => simp [sideLength]
  | succ n ih => simp only [sideLength]; omega

/-- The lower inscribed cube of an n-supertile has side 2^n. -/
theorem floorIter_low_cube {p : Nat} (n : Nat) (c : Cell p)
    (hc : ∀ i, 0 ≤ c i ∧ c i < sideLength n) : floorIter n c = (fun _ => 0) := by
  induction n generalizing c with
  | zero =>
    funext i
    have hi := hc i
    simp only [sideLength] at hi
    change c i = 0
    omega
  | succ n ih =>
    apply ih (floorCell c)
    intro i
    have hi := hc i
    simp only [sideLength] at hi
    change 0 ≤ c i / 2 ∧ c i / 2 < sideLength n
    omega

theorem low_cube_cover (P : Parameters) (n : Nat) (c : Cell P.p)
    (hc : ∀ i, 0 ≤ c i ∧ c i < sideLength n) :
    ∃ t, Descendant P n (identityPose P.p) t ∧ Occupies t c := by
  apply finite_cover P n (identityPose P.p) c
  rw [floorIter_low_cube n c hc]
  apply (identity_occupies _).mpr
  exact ⟨fun _ => Or.inl rfl, ⟨⟨0, by have := P.prime.two_le; omega⟩, rfl⟩⟩

/-- Every finite coordinate vector has one finite symmetric integer bound. -/
theorem cell_has_bound {p : Nat} (c : Cell p) :
    ∃ k : Nat, ∀ i, -(k : Int) ≤ c i ∧ c i < (k : Int) + 1 := by
  have scalar : ∀ z : Int, ∃ k : Nat, -(k : Int) ≤ z ∧ z < (k : Int) + 1 := by
    intro z
    cases z with
    | ofNat n =>
      refine ⟨n, ?_⟩
      change -(n : Int) ≤ (n : Int) ∧ (n : Int) < (n : Int) + 1
      omega
    | negSucc n => exact ⟨n + 1, by omega, by omega⟩
  induction p with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ p ih =>
    obtain ⟨k, hk⟩ := ih (fun i => c i.succ)
    obtain ⟨l, hl⟩ := scalar (c 0)
    refine ⟨max k l, fun i => ?_⟩
    have hmk := Nat.le_max_left k l
    have hml := Nat.le_max_right k l
    refine Fin.cases ?_ (fun j => ?_) i
    · omega
    · have hj := hk j
      omega

end RegisteredPrime.WorldExistence
