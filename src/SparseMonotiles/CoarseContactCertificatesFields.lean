module

public import SparseMonotiles.CoarseContactCertificatesPacked
public import SparseMonotiles.CarrierHierarchyCoarseSymmetry

@[expose] public section

/-!
Field-level exact arithmetic for conjugated representative rows. The encoding
is bound to an actual Pose before use. Coordinate conjugation is computed on
fields, so no separately checked table for every symmetry image is required.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

structure CoarseFields where
  axis : ℕ → ℕ
  negative : ℕ → Bool
  shift : ℕ → ℤ

def CoarseFields.sign (f : CoarseFields) (i : ℕ) : ℤ := if f.negative i then -1 else 1

def CoarseFields.packed (code : ℕ) : CoarseFields :=
  ⟨packedAxis code, packedNegative code, packedShift code⟩

def CoarseFields.Represents {d : ℕ} (f : CoarseFields) (p : Pose d) : Prop := ∀ i : Fin d,
  f.axis i.val = (p.perm i).val ∧ f.negative i.val = p.negative i ∧ f.shift i.val = p.shift i

theorem CoarseFields.packed_represents {d : ℕ} {code : ℕ} {p : Pose d}
    (h : PackedRepresents code p) : (CoarseFields.packed code).Represents p := h

def CoarseFields.conjugate (axis inverse : ℕ → ℕ) (f : CoarseFields) : CoarseFields :=
  ⟨fun i => inverse (f.axis (axis i)), fun i => f.negative (axis i), fun i => f.shift (axis i)⟩

theorem CoarseFields.conjugate_represents {d : ℕ} (r : Equiv.Perm (Fin d))
    (axis inverse : ℕ → ℕ)
    (ha : ∀ i : Fin d, axis i.val = (r i).val)
    (hi : ∀ i : Fin d, inverse i.val = (r.symm i).val)
    {f : CoarseFields} {p : Pose d} (hf : f.Represents p) :
    (f.conjugate axis inverse).Represents (conjugatePose r p) := by
  intro i
  have hp := hf (r i)
  change inverse (f.axis (axis i.val)) = ((conjugatePose r p).perm i).val ∧
    f.negative (axis i.val) = (conjugatePose r p).negative i ∧
    f.shift (axis i.val) = (conjugatePose r p).shift i
  rw [ha i, hp.1, hi (p.perm (r i))]
  exact ⟨rfl, hp.2.1.trans (conjugatePose_negative r p i).symm,
    hp.2.2.trans (conjugatePose_shift r p i).symm⟩

def coarseFieldsProductCheck (d : ℕ) (a b k F : CoarseFields) : Bool :=
  (List.range d).all fun i =>
    decide (b.axis (F.axis i) = k.axis (a.axis i)) &&
    decide (xor (F.negative i) (b.negative (F.axis i)) =
      xor (a.negative i) (k.negative (a.axis i))) &&
    decide (F.sign i * b.shift (F.axis i) + F.shift i =
      a.sign i * k.shift (a.axis i) + a.shift i)

theorem coarseFieldsProductCheck_sound {d : ℕ} {a b k F : Pose d}
    {ac bc kc Fc : CoarseFields}
    (ha : ac.Represents a) (hb : bc.Represents b) (hk : kc.Represents k)
    (hF : Fc.Represents F) (h : coarseFieldsProductCheck d ac bc kc Fc = true) :
    parentCandidate a b k = F := by
  apply coarseProductMatchB_sound
  unfold coarseProductMatchB coarsePoseMatchB
  apply List.all_eq_true.mpr
  intro i _
  have hraw := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hai := ha i
  have hFi := hF i
  have hbFi := hb (F.perm i)
  have hkai := hk (a.perm i)
  simp only [CoarseFields.sign, hai.1, hFi.1, hai.2.1, hFi.2.1, hai.2.2, hFi.2.2,
    hbFi.1, hbFi.2.1, hbFi.2.2, hkai.1, hkai.2.1, hkai.2.2,
    Bool.and_eq_true, decide_eq_true_eq] at hraw
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Fin.ext hraw.1.1
  · exact hraw.1.2
  · exact hraw.2

def coarseFieldsAddressCheck {ρ : Type*} (d : ℕ) (lookup : ρ → CoarseFields)
    (a b k : CoarseFields) (pa pb pk : ℤ) : Option ρ → Bool
  | none => decide ((pa + pk - pb) % 2 ≠ 0)
  | some i => coarseFieldsProductCheck d a b k (lookup i)

theorem coarseFieldsAddressCheck_sound {d : ℕ} {ρ : Type*}
    (lookup : ρ → Pose d) (fields : ρ → CoarseFields) (j : Fin d)
    (hfields : ∀ i, (fields i).Represents (lookup i))
    {a b k : Pose d} {ac bc kc : CoarseFields}
    (ha : ac.Represents a) (hb : bc.Represents b) (hk : kc.Represents k) {pa pb pk : ℤ}
    (hap : ∀ i, a.shift i % 2 = pa % 2) (hbp : ∀ i, b.shift i % 2 = pb % 2)
    (hkp : ∀ i, k.shift i % 2 = pk % 2) {address : Option ρ}
    (h : coarseFieldsAddressCheck d fields ac bc kc pa pb pk address = true)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ i, parentCandidate a b k = lookup i := by
  cases address with
  | none =>
      have hn : (pa + pk - pb) % 2 ≠ 0 := of_decide_eq_true h
      exact False.elim (hn ((parentCandidate_shift_parity a b k pa pb pk hap hbp hkp j).symm.trans
        (heven j)))
  | some i => exact ⟨i, coarseFieldsProductCheck_sound ha hb hk (hfields i) h⟩

#print axioms CoarseFields.conjugate_represents
#print axioms coarseFieldsAddressCheck_sound
end SparseMonotiles.CarrierHierarchy
