module

public import SparseMonotiles.CoarseContactCertificatesParity

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Ten-bit coordinate fields: three permutation bits, one sign bit, and a
six-bit integer displacement biased by16. This is only a checked encoding. -/
def packedAxis (code i : ℕ) : ℕ := code / 1024 ^ i % 8
def packedNegative (code i : ℕ) : Bool := decide (code / (1024 ^ i * 8) % 2 = 1)
def packedShift (code i : ℕ) : ℤ := (code / (1024 ^ i * 16) % 64 : ℕ) - 16
def packedSign (code i : ℕ) : ℤ := if packedNegative code i then -1 else 1

def packedProductCheck (d a b k F : ℕ) : Bool :=
  (List.range d).all fun i =>
    decide (packedAxis b (packedAxis F i) = packedAxis k (packedAxis a i)) &&
    decide (xor (packedNegative F i) (packedNegative b (packedAxis F i)) =
      xor (packedNegative a i) (packedNegative k (packedAxis a i))) &&
    decide (packedSign F i * packedShift b (packedAxis F i) + packedShift F i =
      packedSign a i * packedShift k (packedAxis a i) + packedShift a i)

def PackedRepresents {d : ℕ} (code : ℕ) (p : Pose d) : Prop := ∀ i : Fin d,
  packedAxis code i.val = (p.perm i).val ∧
  packedNegative code i.val = p.negative i ∧ packedShift code i.val = p.shift i

def packedRepresentsB {d : ℕ} (code : ℕ) (p : Pose d) : Bool :=
  (List.finRange d).all fun i =>
    decide (packedAxis code i.val = (p.perm i).val) &&
    decide (packedNegative code i.val = p.negative i) &&
    decide (packedShift code i.val = p.shift i)

theorem packedRepresentsB_sound {d : ℕ} {code : ℕ} {p : Pose d}
    (h : packedRepresentsB code p = true) : PackedRepresents code p := by
  simpa [packedRepresentsB, PackedRepresents, List.all_eq_true, and_assoc] using h

/-- A raw arithmetic product check is accepted only after every input field
has been bound to its actual signed-affine Pose value. -/
theorem packedProductCheck_sound {d : ℕ} {a b k F : Pose d} {ac bc kc Fc : ℕ}
    (ha : PackedRepresents ac a) (hb : PackedRepresents bc b)
    (hk : PackedRepresents kc k) (hF : PackedRepresents Fc F)
    (h : packedProductCheck d ac bc kc Fc = true) : parentCandidate a b k = F := by
  apply coarseProductMatchB_sound
  unfold coarseProductMatchB coarsePoseMatchB
  apply List.all_eq_true.mpr
  intro i _
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hai := ha i
  have hFi := hF i
  have hbFi := hb (F.perm i)
  have hkai := hk (a.perm i)
  simp only [packedSign, hai.1, hFi.1, hai.2.1, hFi.2.1, hai.2.2, hFi.2.2,
    hbFi.1, hbFi.2.1, hbFi.2.2, hkai.1, hkai.2.1, hkai.2.2,
    Bool.and_eq_true, decide_eq_true_eq] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Fin.ext
    exact hi.1.1
  · exact hi.1.2
  · exact hi.2

def packedAddressCheck {ρ : Type*} (d : ℕ) (lookup : ρ → ℕ)
    (a b k : ℕ) (pa pb pk : ℤ) : Option ρ → Bool
  | none => decide ((pa + pk - pb) % 2 ≠ 0)
  | some i => packedProductCheck d a b k (lookup i)

theorem packedAddressCheck_sound {d : ℕ} {ρ : Type*}
    (lookup : ρ → Pose d) (codes : ρ → ℕ) (j : Fin d)
    (hcodes : ∀ i, PackedRepresents (codes i) (lookup i))
    {a b k : Pose d} {ac bc kc : ℕ}
    (ha : PackedRepresents ac a) (hb : PackedRepresents bc b)
    (hk : PackedRepresents kc k) {pa pb pk : ℤ}
    (hap : ∀ i, a.shift i % 2 = pa % 2) (hbp : ∀ i, b.shift i % 2 = pb % 2)
    (hkp : ∀ i, k.shift i % 2 = pk % 2) {address : Option ρ}
    (h : packedAddressCheck d codes ac bc kc pa pb pk address = true)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ i, parentCandidate a b k = lookup i := by
  cases address with
  | none =>
      have hn : (pa + pk - pb) % 2 ≠ 0 := of_decide_eq_true h
      exact False.elim (hn ((parentCandidate_shift_parity a b k pa pb pk hap hbp hkp j).symm.trans
        (heven j)))
  | some i => exact ⟨i, packedProductCheck_sound ha hb hk (hcodes i) h⟩

#print axioms packedProductCheck_sound
#print axioms packedAddressCheck_sound
end SparseMonotiles.CarrierHierarchy
