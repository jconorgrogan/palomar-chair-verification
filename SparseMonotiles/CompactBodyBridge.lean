module

public import SparseMonotiles.CompactStatement
public import SparseMonotiles.Model

@[expose] public section

/-! Exact type/solid/union transport from the independent compact statement
into the frozen model. Finite list equality is proved separately, not assumed
from generator hashes or existential canonical-pyramid statements. -/
namespace SparseMonotiles.CompactBinding

/-- The two key structures have exactly the same rational geometric fields. -/
def toKeyData {d : ℕ} (k : PalomarMonotiles.Key d) : KeyData d :=
  ⟨k.centre, k.radius, k.apex, k.bump⟩

instance {d : ℕ} : DecidableEq (KeyData d) := fun a b =>
  decidable_of_iff (a.centre = b.centre ∧ a.radius = b.radius ∧ a.apex = b.apex ∧ a.bump = b.bump)
    (by cases a; cases b; simp only [KeyData.mk.injEq])

theorem keySolid_toKeyData {d : ℕ} (k : PalomarMonotiles.Key d) :
    SparseMonotiles.keySolid (toKeyData k) = PalomarMonotiles.keySolid k := rfl

theorem carrier_eq (d : ℕ) : SparseMonotiles.carrier d = PalomarMonotiles.carrier d := rfl

theorem keyUnion_map {d : ℕ} (ks : List (PalomarMonotiles.Key d)) (b : Bool) :
    SparseMonotiles.keyUnion (ks.map toKeyData) b = PalomarMonotiles.keyUnion ks b := by
  ext x
  change (∃ k ∈ ks.map toKeyData, k.bump = b ∧ x ∈ SparseMonotiles.keySolid k) ↔
    ∃ k ∈ ks, k.bump = b ∧ x ∈ PalomarMonotiles.keySolid k
  constructor
  · rintro ⟨k, hk, hb, hx⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
    exact ⟨u, hu, hb, hx⟩
  · rintro ⟨k, hk, hb, hx⟩
    exact ⟨toKeyData k, List.mem_map.mpr ⟨k, hk, rfl⟩, hb, hx⟩

theorem body_map {d : ℕ} (ks : List (PalomarMonotiles.Key d)) :
    SparseMonotiles.body (ks.map toKeyData) = PalomarMonotiles.body ks := by
  simp only [SparseMonotiles.body, PalomarMonotiles.body, keyUnion_map, carrier_eq]

/-- The independent statement retains the exact arbitrary-isometry tiling notion. -/
theorem tiling_iff {d : ℕ} (T : Set (Point d)) (tiles : Set (Set (Point d))) :
    SparseMonotiles.IsTiling T tiles ↔ PalomarMonotiles.IsTiling T tiles := Iff.rfl

/-- Physical tile-collection periods, not mere invariance of the union. -/
theorem period_iff {d : ℕ} (tiles : Set (Set (Point d))) (v : Point d) :
    SparseMonotiles.IsPeriod tiles v ↔ PalomarMonotiles.IsPeriod tiles v := Iff.rfl

theorem monotile_iff {d : ℕ} (T : Set (Point d)) :
    SparseMonotiles.IsAperiodicMonotile T ↔ PalomarMonotiles.IsAperiodicMonotile T := Iff.rfl

#print axioms keySolid_toKeyData
#print axioms body_map
#print axioms monotile_iff
end SparseMonotiles.CompactBinding
