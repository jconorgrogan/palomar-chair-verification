module

public import SparseMonotiles.CarrierHierarchyBoxes
public import SparseMonotiles.CarrierHierarchyFan

@[expose] public section

/-!
The local fan premises are derived from actual registered occupied-cell coverage,
nonoverlap, and explicit catalog properties. This closes the combinatorial
recognition step without assuming complete stars as an input. The conversion
from an arbitrary physical tiling to this registered local patch remains open.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def wallBox {d : ℕ} (j : Fin d) (b : Bool) : Cell d :=
  fun i => if i = j then if b then 2 else -2 else 0

private theorem wallBox_pos {d : ℕ} (j : Fin d) :
    wallBox j true = fun i => 2 * unitAxis j i := by
  funext i
  by_cases h : i = j <;> simp [wallBox, unitAxis, h]

private theorem wallBox_neg {d : ℕ} (j : Fin d) :
    wallBox j false = fun i => -2 * unitAxis j i := by
  funext i
  by_cases h : i = j <;> simp [wallBox, unitAxis, h]

private theorem wallBox_injective {d : ℕ} {j k : Fin d} {b c : Bool}
    (h : wallBox j b = wallBox k c) : j = k ∧ b = c := by
  have hj := congrFun h j
  have hjk : j = k := by
    by_contra hh
    cases b <;> simp [wallBox, hh] at hj
  subst k
  refine ⟨rfl, ?_⟩
  cases b <;> cases c <;> simp [wallBox] at hj ⊢

/-- Every legal wall along a nonempty root role owns that exterior cell. The
empty-role exception at a negative complement wall is deliberately retained. -/
theorem wall_owns_exterior {d : ℕ} {p : Pose d} (hw : WallGeometry p)
    {a : Bits d} (ha : Proper a) (hna : NonemptyRole a) (j : Fin d)
    (hb : boxLower p = wallBox j (a j)) : Occupies p (exterior a j) := by
  apply (occupies_box_iff p _).mpr
  constructor
  · intro i
    rw [congrFun hb i]
    by_cases hij : i = j
    · subst i
      cases h : a j <;> simp [wallBox, exterior, bit, h]
    · cases h : a i <;> simp [wallBox, exterior, bit, h, hij]
  · intro he
    obtain ⟨k, h | h⟩ := hw
    · have hh : wallBox j (a j) = wallBox k true := by
        rw [wallBox_pos]
        exact hb.symm.trans h.1
      obtain ⟨rfl, haj⟩ := wallBox_injective hh
      rcases h.2 with hh | hh
      · obtain ⟨i, hi⟩ := ha
        have hij : i ≠ j := by intro hij; subst i; simp [haj] at hi
        have hx := congrFun (he.trans hh) i
        simp [exterior, bit, hi, hij, unitAxis] at hx
      · have hx := congrFun (he.trans hh) j
        simp [exterior, bit, haj, unitAxis] at hx
    · have hh : wallBox j (a j) = wallBox k false := by
        rw [wallBox_neg]
        exact hb.symm.trans h.1
      obtain ⟨rfl, haj⟩ := wallBox_injective hh
      rcases h.2 with hh | hh
      · have hx := congrFun (he.trans hh) j
        simp [exterior, bit, haj, unitAxis] at hx
      · obtain ⟨i, hi⟩ := hna
        have hij : i ≠ j := by intro hij; subst i; simp [haj] at hi
        have hx := congrFun (he.trans hh) i
        simp [exterior, bit, hi, hij, unitAxis] at hx

/-- A normalized local patch around the root chair. Every assumption is about
concrete unit cells or individual listed relative poses. -/
structure LocalPatch (d : ℕ) (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) where
  tiles : Set (Pose d)
  catalog : ∀ p ∈ tiles, LocalCatalogFacts σ r p
  covers : ∀ a, Proper a → ∀ j, ∃ p ∈ tiles, Occupies p (exterior a j)
  root_disjoint : ∀ p ∈ tiles, ∀ a, Proper a → ¬ Occupies p (fun i => bit a i)
  disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
    Occupies p c → Occupies q c → p = q

def LocalPatch.incoming {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (P : LocalPatch d σ r) (a : Bits d) : Prop :=
  ∃ p ∈ P.tiles, GaugeRel r (incomingPose a (σ a)) p

def LocalPatch.wall {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (P : LocalPatch d σ r) (j : Fin d) (b : Bool) : Prop :=
  ∃ p ∈ P.tiles, boxLower p = wallBox j b

private theorem shift_parity_box {d : ℕ} (p : Pose d) (b : Bool)
    (h : ∀ i, p.shift i % 2 = if b then 1 else 0) :
    ∀ i, boxLower p i % 2 = if b then 1 else 0 := by
  intro i
  have hi := h i
  cases hn : p.negative i <;> simp [boxLower, hn] <;> omega

/-- The fan coverage implication is proved from complete outside-cell coverage
and the exhaustive two-box calculation. -/
theorem LocalPatch.cover {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (P : LocalPatch d σ r)
    (a : Bits d) (ha : Proper a) (j : Fin d) (hn : ¬ P.incoming a) :
    P.wall j (a j) := by
  obtain ⟨p, hp, hx⟩ := P.covers a ha j
  have hc := P.catalog p hp
  obtain ⟨b, hb⟩ := hc.1
  have hbox := shift_parity_box p b hb
  cases b with
  | false =>
      refine ⟨p, hp, ?_⟩
      have he := even_exterior_box p a j hx hbox
      rw [he]
      funext i
      by_cases hij : i = j
      · subst i
        cases h : a j <;> simp [wallBox, bit, h]
      · simp [wallBox, hij]
  | true =>
      have hh := odd_exterior_hole p a j hx hbox (P.root_disjoint p hp a ha)
      have hrole := role_of_box_and_hole (odd_exterior_box p a j hx hbox) hh
      have hi : IsChairCell (hole p) := by
        rw [hh]
        constructor
        · intro i
          cases h : a i <;> simp [bit, h]
        · obtain ⟨i, hi⟩ := ha
          exact ⟨i, by simp [bit, hi]⟩
      have hg := (hc.2.1 hi).2
      exact False.elim (hn ⟨p, hp, by simpa [hrole] using hg⟩)

/-- The fan exclusion implication is proved from actual overlap of the
computed outside cell, not postulated as a global recognition property. -/
theorem LocalPatch.exclude {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (P : LocalPatch d σ r)
    (a : Bits d) (ha : Proper a) (hna : NonemptyRole a) (hi : P.incoming a)
    (j : Fin d) : ¬ P.wall j (a j) := by
  rintro ⟨q, hq, hbq⟩
  obtain ⟨p, hp, hgp⟩ := hi
  have hpx : Occupies p (exterior a j) :=
    (gauge_occupies_iff hgp _).mp (incoming_owns_exterior a (σ a) j)
  have hqe : ∀ i, q.shift i % 2 = 0 := by
    intro i
    have hh := congrFun hbq i
    by_cases hij : i = j <;> cases hn : q.negative i <;> cases ha' : a j <;>
      simp [boxLower, wallBox, hn, ha', hij] at hh ⊢ <;> omega
  have hqx := wall_owns_exterior ((P.catalog q hq).2.2 hqe) ha hna j hbq
  have he := P.disjoint p hp q hq _ hpx hqx
  have hpb : boxLower p = fun i => 2 * bit a i - 1 := by
    rcases hgp with rfl | rfl
    · exact incoming_boxLower a (σ a)
    · exact incoming_boxLower a (σ a)
  have hc := congrFun (hpb.symm.trans (he ▸ hbq)) j
  cases haj : a j <;> simp [bit, wallBox, haj] at hc

/-- A concrete local registered patch now supplies the previously generic fan. -/
def LocalPatch.fanData {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (P : LocalPatch d σ r) : FanData d where
  incoming := P.incoming
  wall := P.wall
  cover := P.cover
  exclude := P.exclude

/-- Nontrivial recognition theorem from registered cell coverage and the exact
individual-contact catalog properties. It does not assume any complete star. -/
theorem LocalPatch.complete_of_nonempty_incoming {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (P : LocalPatch d σ r) (hd : 3 ≤ d) {a : Bits d}
    (ha : Proper a) (hna : NonemptyRole a) (hi : P.incoming a) :
    ∀ b, Proper b → P.incoming b :=
  P.fanData.complete_of_nonempty_incoming hd ha hna hi

#print axioms wall_owns_exterior
#print axioms LocalPatch.cover
#print axioms LocalPatch.exclude
#print axioms LocalPatch.complete_of_nonempty_incoming
end SparseMonotiles.CarrierHierarchy
