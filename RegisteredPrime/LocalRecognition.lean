module
public import RegisteredPrime.BoxGeometry
public import RegisteredPrime.Fan
@[expose] public section
namespace RegisteredPrime
def unitAxis {p : Nat} (j : Fin p) : Cell p := fun i => if i = j then 1 else 0
def WallGeometry {p : Nat} (q : Pose p) : Prop := ∃ j,
  (boxLower q = wallBox j true ∧
    (hole q = (fun i => 1 + unitAxis j i) ∨ hole q = (fun i => 3 * unitAxis j i))) ∨
  (boxLower q = wallBox j false ∧
    (hole q = (fun i => 1 - 3 * unitAxis j i) ∨ hole q = (fun i => -unitAxis j i)))
def IncomingSupport {p : Nat} (q : Pose p) (A : Mask p) : Prop :=
  boxLower q = (fun i => 2 * bit (A i) - 1) ∧ hole q = (fun i => bit (A i))
theorem incoming_owns_exterior {p : Nat} (q : Pose p) (A : Mask p)
    (hq : IncomingSupport q A) (j : Fin p) : Occupies q (exterior A j) := by
  apply (occupies_box_iff q _).mpr
  rw [hq.1, hq.2]
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      cases h : A j <;> simp [exterior, bit, h]
    · cases h : A i <;> simp [exterior, bit, h, hij]
  · intro h
    have hj := congrFun h j
    cases h : A j <;> simp [exterior, bit, h] at hj
theorem wallBox_injective {p : Nat} {j k : Fin p} {b c : Bool}
    (h : wallBox j b = wallBox k c) : j = k ∧ b = c := by
  have hj := congrFun h j
  have hjk : j = k := by
    apply Classical.byContradiction
    intro hh
    cases b <;> simp [wallBox, hh] at hj
  subst k
  refine ⟨rfl, ?_⟩
  cases b <;> cases c <;> simp [wallBox] at hj ⊢
theorem wall_owns_exterior {p : Nat} {q : Pose p} (hw : WallGeometry q)
    {A : Mask p} (hA : Proper A) (hnA : NonemptyMask A) (j : Fin p)
    (hb : boxLower q = wallBox j (A j)) : Occupies q (exterior A j) := by
  apply (occupies_box_iff q _).mpr
  constructor
  · intro i
    rw [congrFun hb i]
    by_cases hij : i = j
    · subst i
      cases h : A j <;> simp [wallBox, exterior, bit, h]
    · cases h : A i <;> simp [wallBox, exterior, bit, h, hij]
  · intro he
    obtain ⟨k, h | h⟩ := hw
    · obtain ⟨rfl, haj⟩ := wallBox_injective (hb.symm.trans h.1)
      rcases h.2 with hh | hh
      · obtain ⟨i, hi⟩ := hA
        have hij : i ≠ j := by intro hij; subst i; simp [haj] at hi
        have hx := congrFun (he.trans hh) i
        simp [exterior, bit, hi, hij, unitAxis] at hx
      · have hx := congrFun (he.trans hh) j
        simp [exterior, bit, haj, unitAxis] at hx
    · obtain ⟨rfl, haj⟩ := wallBox_injective (hb.symm.trans h.1)
      rcases h.2 with hh | hh
      · have hx := congrFun (he.trans hh) j
        simp [exterior, bit, haj, unitAxis] at hx
      · obtain ⟨i, hi⟩ := hnA
        have hij : i ≠ j := by intro hij; subst i; simp [haj] at hi
        have hx := congrFun (he.trans hh) i
        simp [exterior, bit, hi, hij, unitAxis] at hx
structure LocalPatch (p : Nat) where
  tiles : Pose p → Prop
  parity : ∀ q, tiles q → q.UniformParity
  walls : ∀ q, tiles q → (∀ i, q.anchor i % 2 = 0) → WallGeometry q
  covers : ∀ A, Proper A → ∀ j, ∃ q, tiles q ∧ Occupies q (exterior A j)
  root_disjoint : ∀ q, tiles q → ∀ A, Proper A → ¬ Occupies q (fun i => bit (A i))
  nonoverlap : ∀ q r, tiles q → tiles r → ∀ c,
    Occupies q c → Occupies r c → q.Same r
def LocalPatch.incoming {p : Nat} (L : LocalPatch p) (A : Mask p) : Prop :=
  ∃ q, L.tiles q ∧ IncomingSupport q A
def LocalPatch.wall {p : Nat} (L : LocalPatch p) (j : Fin p) (b : Bool) : Prop :=
  ∃ q, L.tiles q ∧ boxLower q = wallBox j b
theorem LocalPatch.cover {p : Nat} (L : LocalPatch p) (A : Mask p) (hA : Proper A)
    (j : Fin p) (hn : ¬ L.incoming A) : L.wall j (A j) := by
  obtain ⟨q, hq, hx⟩ := L.covers A hA j
  obtain ⟨b, hb⟩ := L.parity q hq
  have hbox := uniform_parity_box q b hb
  cases b with
  | false => exact ⟨q, hq, even_exterior_box q A j hx hbox⟩
  | true =>
    exact False.elim (hn ⟨q, hq, odd_exterior_box q A j hx hbox,
      odd_exterior_hole q A j hx hbox (L.root_disjoint q hq A hA)⟩)
theorem Pose.Same.boxLower {p : Nat} {q r : Pose p} (h : q.Same r) :
    RegisteredPrime.boxLower q = RegisteredPrime.boxLower r := by
  funext i
  simp only [RegisteredPrime.boxLower]
  rw [h.2.1 i, h.2.2 i]
theorem LocalPatch.exclude {p : Nat} (L : LocalPatch p) (A : Mask p)
    (hA : Proper A) (hnA : NonemptyMask A) (hin : L.incoming A) (j : Fin p) :
    ¬ L.wall j (A j) := by
  rintro ⟨r, hr, hbr⟩
  obtain ⟨q, hq, hqin⟩ := hin
  have hqe := incoming_owns_exterior q A hqin j
  have hreven : ∀ i, r.anchor i % 2 = 0 := by
    intro i
    have h := congrFun hbr i
    by_cases hij : i = j <;> cases hn : r.frame.negative i <;> cases ha : A j <;>
      simp [boxLower, wallBox, bit, hn, ha, hij] at h ⊢ <;> omega
  have hre := wall_owns_exterior (L.walls r hr hreven) hA hnA j hbr
  have he := L.nonoverlap q r hq hr _ hqe hre
  have hc := congrFun (hqin.1.symm.trans (he.boxLower.trans hbr)) j
  cases h : A j <;> simp [bit, wallBox, h] at hc
def LocalPatch.fanData {p : Nat} (L : LocalPatch p) : FanData p where
  incoming := L.incoming
  wall := L.wall
  cover := L.cover
  exclude := L.exclude
theorem LocalPatch.complete_of_nonempty_incoming {p : Nat} (L : LocalPatch p)
    (hp : 3 ≤ p) {A : Mask p} (hA : Proper A) (hnA : NonemptyMask A)
    (hin : L.incoming A) : ∀ B, Proper B → L.incoming B :=
  L.fanData.complete_of_nonempty_incoming hp hA hnA hin
end RegisteredPrime
