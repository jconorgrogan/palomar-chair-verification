module

public import SparseMonotiles.CandidateCompleteness
public import SparseMonotiles.ContactCertificateFullTools

@[expose] public section

/-!
# Local certificates binding the pair generator to replay rows

A certificate is checked separately for every ordered pair of key indices. It
records either failure of the generator, an exact lookup into the replay table,
or two explicit carrier cells that overlap in the generated pose. No theorem
below assumes that the generated poses are covered by the rows. The premises
are executable local equations and finite key/row lookup bindings.

The row-address type is arbitrary, so generated data may use a dependent pair of
chunk and bounded local slot, with balanced lookup functions. This avoids both
a scan through all replay rows and evaluation of the large `Finset.biUnion`.
Arbitrary physical placement registration is not addressed here.
-/
namespace SparseMonotiles.Contact

/-- Flat key indices retain their facet owner. The two binding fields are small
per-facet finite checks; they do not mention generated poses or replay rows. -/
structure KeyIndexing {d n : ℕ} (g : IndexedGeometry d n) (m : ℕ) where
  facet : Fin m → Fin n
  key : Fin m → BoxKey d
  profileIndices : Fin n → Finset (Fin m)
  profile_eq : ∀ i, g.profile i = (profileIndices i).image key
  owner_eq : ∀ i a, a ∈ profileIndices i → facet a = i

theorem KeyIndexing.covers {d n m : ℕ} {g : IndexedGeometry d n}
    (keys : KeyIndexing g m) {i : Fin n} {k : BoxKey d} (hk : k ∈ g.profile i) :
    ∃ a : Fin m, keys.facet a = i ∧ keys.key a = k := by
  rw [keys.profile_eq i] at hk
  rcases Finset.mem_image.mp hk with ⟨a, ha, he⟩
  exact ⟨a, keys.owner_eq i a ha, he⟩

/-- Build a flat key enumeration from short per-facet index lists. The owner
check deliberately uses `List.all`, avoiding a full finite key-universe scan. -/
def KeyIndexing.ofLists {d n m : ℕ} {g : IndexedGeometry d n}
    (owner : Fin m → Fin n) (key : Fin m → BoxKey d)
    (indices : Fin n → List (Fin m))
    (profile_eq : ∀ i, ((indices i).map key).toFinset = g.profile i)
    (owner_checked : ∀ i, (indices i).all (fun a => decide (owner a = i)) = true) :
    KeyIndexing g m where
  facet := owner
  key := key
  profileIndices := fun i => (indices i).toFinset
  profile_eq := by
    intro i
    rw [← profile_eq i]
    ext k
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  owner_eq := by
    intro i a ha
    exact of_decide_eq_true
      (List.all_eq_true.mp (owner_checked i) a (List.mem_toFinset.mp ha))

/-- This local computation uses the same algorithm as `generatedCandidates`. -/
def KeyIndexing.pair {d n m : ℕ} {g : IndexedGeometry d n}
    (keys : KeyIndexing g m) (a b : Fin m) : Option (Pose d) :=
  pairPose g.denominator (g.facet (keys.facet a)) (g.facet (keys.facet b))
    (keys.key a) (keys.key b)

/-- Direct coordinate equality avoids dependent equality recursors in the
standard `DecidableEq (Option (Pose d))` reduction for generated permutations. -/
def Pose.SameCoordinates {d : ℕ} (p q : Pose d) : Prop :=
  ∀ i, p.perm i = q.perm i ∧ p.negative i = q.negative i ∧ p.shift i = q.shift i

instance {d : ℕ} (p q : Pose d) : Decidable (p.SameCoordinates q) :=
  inferInstanceAs (Decidable (∀ i, _ ∧ _ ∧ _))

theorem Pose.eq_of_sameCoordinates {d : ℕ} {p q : Pose d}
    (h : p.SameCoordinates q) : p = q := by
  have hp : p.perm = q.perm := Equiv.ext fun i => (h i).1
  have hn : p.negative = q.negative := funext fun i => (h i).2.1
  have hs : p.shift = q.shift := funext fun i => (h i).2.2
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

/-- The option must contain a pose, and every coordinate of that pose is checked. -/
def optionPoseMatches {d : ℕ} (candidate : Option (Pose d)) (p : Pose d) : Prop :=
  match candidate with
  | none => False
  | some q => q.SameCoordinates p

instance {d : ℕ} (candidate : Option (Pose d)) (p : Pose d) :
    Decidable (optionPoseMatches candidate p) :=
  match candidate with
  | none => inferInstanceAs (Decidable False)
  | some q => inferInstanceAs (Decidable (q.SameCoordinates p))

theorem optionPoseMatches_eq_some {d : ℕ} {candidate : Option (Pose d)} {p : Pose d}
    (h : optionPoseMatches candidate p) : candidate = some p := by
  cases candidate with
  | none => exact h.elim
  | some q => exact congrArg some (Pose.eq_of_sameCoordinates h)

/-- A row address can be a packed chunk/local index, rather than a global list
index. Overlap exclusions carry both cells and are checked against the pose. -/
inductive GeneratorPairCertificate (d : ℕ) (ρ : Type*) where
  | absent
  | row (address : ρ)
  | overlap (rootCell sourceCell : Cell d)

/-- All three cases are local decidable propositions. An `absent` certificate
cannot hide a generated pose, and an overlap is verified by exact cell action. -/
def GeneratorPairCertificate.Valid {d : ℕ} {ρ : Type*} (cells : Finset (Cell d))
    (lookup : ρ → Pose d) (candidate : Option (Pose d)) :
    GeneratorPairCertificate d ρ → Prop
  | .absent => candidate = none
  | .row address => optionPoseMatches candidate (lookup address)
  | .overlap root source => root ∈ cells ∧ source ∈ cells ∧
      match candidate with
      | none => False
      | some p => p.cell source = root

instance {d : ℕ} {ρ : Type*} (cells : Finset (Cell d))
    (lookup : ρ → Pose d) (candidate : Option (Pose d)) :
    (cert : GeneratorPairCertificate d ρ) → Decidable (cert.Valid cells lookup candidate)
  | .absent => inferInstanceAs (Decidable (_ = _))
  | .row _ => inferInstanceAs (Decidable (optionPoseMatches _ _))
  | .overlap _ _ =>
      match candidate with
      | none => inferInstanceAs (Decidable (_ ∧ _ ∧ False))
      | some _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Soundness of one certificate: an existing carrier-disjoint pose must have
an exact replay lookup witness. No property of the verdict is used here. -/
theorem GeneratorPairCertificate.sound {d : ℕ} {ρ : Type*}
    {cells : Finset (Cell d)} {lookup : ρ → Pose d}
    {candidate : Option (Pose d)} {cert : GeneratorPairCertificate d ρ}
    (checked : cert.Valid cells lookup candidate) {p : Pose d}
    (generated : candidate = some p) (disjoint : Disjoint cells (cells.image p.cell)) :
    ∃ address, lookup address = p := by
  cases cert with
  | absent =>
      change candidate = none at checked
      rw [generated] at checked
      cases checked
  | row address =>
      have he := optionPoseMatches_eq_some checked
      exact ⟨address, Option.some.inj (he.symm.trans generated)⟩
  | overlap root source =>
      change root ∈ cells ∧ source ∈ cells ∧ _ at checked
      have action : p.cell source = root := by simpa [generated] using checked.2.2
      exact (Finset.disjoint_left.mp disjoint checked.1
        (Finset.mem_image.mpr ⟨source, checked.2.1, action⟩)).elim

/-- O(d) chair occupancy can certify the overlap branch without enumerating the
carrier set. The exact action equation is still checked. -/
def GeneratorPairCertificate.ChairValid {d : ℕ} {ρ : Type*}
    (lookup : ρ → Pose d) (candidate : Option (Pose d)) :
    GeneratorPairCertificate d ρ → Prop
  | .absent => candidate = none
  | .row address => optionPoseMatches candidate (lookup address)
  | .overlap root source => IsChairCell root ∧ IsChairCell source ∧
      match candidate with
      | none => False
      | some p => p.cell source = root

instance {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d) (candidate : Option (Pose d)) :
    (cert : GeneratorPairCertificate d ρ) → Decidable (cert.ChairValid lookup candidate)
  | .absent => inferInstanceAs (Decidable (_ = _))
  | .row _ => inferInstanceAs (Decidable (optionPoseMatches _ _))
  | .overlap _ _ =>
      match candidate with
      | none => inferInstanceAs (Decidable (_ ∧ _ ∧ False))
      | some _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem GeneratorPairCertificate.chairValid_valid {d : ℕ} {ρ : Type*}
    {cells : Finset (Cell d)} (cells_eq : cells = chairCells d)
    {lookup : ρ → Pose d} {candidate : Option (Pose d)}
    {cert : GeneratorPairCertificate d ρ} (checked : cert.ChairValid lookup candidate) :
    cert.Valid cells lookup candidate := by
  cases cert with
  | absent => exact checked
  | row _ => exact checked
  | overlap root source =>
      exact ⟨by simpa [cells_eq, mem_chairCells] using checked.1,
        by simpa [cells_eq, mem_chairCells] using checked.2.1, checked.2.2⟩

/-- Unpack the mathematical generator, use a local pair certificate, and discard
only a certified overlap. The large generated set is never evaluated. -/
theorem KeyIndexing.generated_lookup_of_checked {d n m : ℕ} {ρ : Type*}
    {g : IndexedGeometry d n} (keys : KeyIndexing g m) (lookup : ρ → Pose d)
    (certificates : Fin m → Fin m → GeneratorPairCertificate d ρ)
    (checked : ∀ a b, (certificates a b).Valid g.cells lookup (keys.pair a b))
    {p : Pose d} (generated : p ∈ g.generatedCandidates)
    (disjoint : Disjoint g.cells (g.cells.image p.cell)) :
    ∃ address, lookup address = p := by
  rcases Finset.mem_biUnion.mp generated with ⟨i, _, hi⟩
  rcases Finset.mem_biUnion.mp hi with ⟨j, _, hj⟩
  rcases Finset.mem_biUnion.mp hj with ⟨root, hroot, hr⟩
  rcases Finset.mem_biUnion.mp hr with ⟨source, hsource, hp⟩
  obtain ⟨a, hai, har⟩ := keys.covers hroot
  obtain ⟨b, hbj, hbs⟩ := keys.covers hsource
  apply GeneratorPairCertificate.sound (checked a b) _ disjoint
  simpa [KeyIndexing.pair, hai, hbj, har, hbs] using hp

/-- The lookup target may also be a plain pose list, allowing replay data to
mix independently sound indexed and slot-based rejection formats. -/
theorem KeyIndexing.generated_mem_list_of_checked {d n m : ℕ} {ρ : Type*}
    {g : IndexedGeometry d n} (keys : KeyIndexing g m) (lookup : ρ → Pose d)
    {poses : List (Pose d)} (lookup_mem : ∀ address, lookup address ∈ poses)
    (certificates : Fin m → Fin m → GeneratorPairCertificate d ρ)
    (checked : ∀ a b, (certificates a b).Valid g.cells lookup (keys.pair a b))
    {p : Pose d} (generated : p ∈ g.generatedCandidates)
    (disjoint : Disjoint g.cells (g.cells.image p.cell)) : p ∈ poses := by
  obtain ⟨address, he⟩ := keys.generated_lookup_of_checked lookup certificates checked
    generated disjoint
  exact he ▸ lookup_mem address

/-- A checked packed row lookup turns a generated-pose witness into actual list
membership. The lookup binding is independent of candidate completeness. -/
theorem KeyIndexing.generated_mem_rows_of_checked {d n m : ℕ} {ρ : Type*}
    {g : IndexedGeometry d n} (keys : KeyIndexing g m) (lookup : ρ → Pose d)
    {rows : List (IndexedRow d n)}
    (lookup_mem : ∀ address, lookup address ∈ rows.map IndexedRow.pose)
    (certificates : Fin m → Fin m → GeneratorPairCertificate d ρ)
    (checked : ∀ a b, (certificates a b).Valid g.cells lookup (keys.pair a b))
    {p : Pose d} (generated : p ∈ g.generatedCandidates)
    (disjoint : Disjoint g.cells (g.cells.image p.cell)) :
    ∃ row ∈ rows, row.pose = p := by
  obtain ⟨address, he⟩ := keys.generated_lookup_of_checked lookup certificates checked
    generated disjoint
  exact List.mem_map.mp (he ▸ lookup_mem address)

/-- Registered literal contact exactness follows from the separately checked
local generator certificates, elementary key facts, and replay verdicts. -/
theorem indexed_contact_language_exact_of_generator_certificates
    {d n m : ℕ} {ρ : Type*} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) (owned : ∀ j, (g.facet j).cell ∈ g.cells)
    (unique : Function.Injective g.facet) (den_ne : g.denominator ≠ 0)
    (nonempty : ∀ i, (g.profile i).Nonempty)
    (validKeys : ∀ i k, k ∈ g.profile i → k.OnFacet g.denominator (g.facet i))
    (asymmetric : ∀ i k, k ∈ g.profile i → k.Asymmetric)
    (keys : KeyIndexing g m) (lookup : ρ → Pose d)
    {rows : List (IndexedRow d n)} (rows_checked : indexedValidate g rows = true)
    (lookup_mem : ∀ address, lookup address ∈ rows.map IndexedRow.pose)
    (certificates : Fin m → Fin m → GeneratorPairCertificate d ρ)
    (checked : ∀ a b, (certificates a b).Valid g.cells lookup (keys.pair a b)) :
    ∀ p, g.LegalContact p ↔ p ∈ indexedAcceptedPoses rows := by
  apply indexed_contact_language_exact_of_complete cells_eq owned unique rows_checked
  intro p legal
  exact keys.generated_mem_rows_of_checked lookup lookup_mem certificates checked
    (IndexedGeometry.legalContact_mem_generatedCandidates den_ne nonempty validKeys
      asymmetric legal) legal.1

/-- Packed addresses permit unequal chunk lengths, including a final short
chunk. All components are bounded before a lookup is evaluated. -/
abbrev PackedRowAddress {c : ℕ} (sizes : Fin c → ℕ) :=
  (block : Fin c) × Fin (sizes block)

def packedPoseLookup {d c : ℕ} {sizes : Fin c → ℕ}
    (lookup : (block : Fin c) → Fin (sizes block) → Pose d)
    (address : PackedRowAddress sizes) : Pose d := lookup address.1 address.2

/-- Exact `ofFn` binding is enough to place every balanced lookup result in its
frozen row chunk. The checker need not scan the complete row list. -/
theorem lookup_mem_of_ofFn {d n m : ℕ} {lookup : Fin m → Pose d}
    {rows : List (IndexedRow d n)}
    (binding : List.ofFn lookup = rows.map IndexedRow.pose) (i : Fin m) :
    lookup i ∈ rows.map IndexedRow.pose := by
  rw [← binding]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Assemble independently bound chunks using only their inclusion into the
final row list. No pose equality search is performed by this theorem. -/
theorem packedLookup_mem_of_chunks {d n c : ℕ} {sizes : Fin c → ℕ}
    {lookup : (block : Fin c) → Fin (sizes block) → Pose d}
    {chunks : Fin c → List (IndexedRow d n)} {rows : List (IndexedRow d n)}
    (binding : ∀ block, List.ofFn (lookup block) = (chunks block).map IndexedRow.pose)
    (included : ∀ block row, row ∈ chunks block → row ∈ rows)
    (address : PackedRowAddress sizes) :
    packedPoseLookup lookup address ∈ rows.map IndexedRow.pose := by
  obtain ⟨row, hr, he⟩ := List.mem_map.mp (lookup_mem_of_ofFn (binding address.1) address.2)
  exact List.mem_map.mpr ⟨row, included address.1 row hr, he⟩

/-- Structural finite-index splitting lets generated proofs combine separately
kernel-checked ranges. This theorem does not run a decider over the full range. -/
theorem forall_fin_add_of_chunks {a b : ℕ} {P : Fin (a + b) → Prop}
    (left : ∀ i : Fin a, P (Fin.castAdd b i))
    (right : ∀ i : Fin b, P (Fin.natAdd a i)) : ∀ i, P i := by
  intro i
  by_cases hi : i.val < a
  · have he : Fin.castAdd b (⟨i.val, hi⟩ : Fin a) = i := Fin.ext rfl
    exact he ▸ left ⟨i.val, hi⟩
  · have hj : i.val - a < b := by omega
    have he : Fin.natAdd a (⟨i.val - a, hj⟩ : Fin b) = i := by
      apply Fin.ext
      simp only [Fin.natAdd_mk]
      omega
    exact he ▸ right ⟨i.val - a, hj⟩

/-- Splitting either pair coordinate yields complete rectangular coverage. The
rectangles can be checked in independent modules and combined recursively. -/
theorem forall_fin_pair_of_chunks {a b m : ℕ} {P : Fin (a + b) → Fin m → Prop}
    (left : ∀ i : Fin a, ∀ j, P (Fin.castAdd b i) j)
    (right : ∀ i : Fin b, ∀ j, P (Fin.natAdd a i) j) : ∀ i j, P i j :=
  forall_fin_add_of_chunks left right

#print axioms GeneratorPairCertificate.sound
#print axioms KeyIndexing.generated_lookup_of_checked
#print axioms indexed_contact_language_exact_of_generator_certificates
#print axioms packedLookup_mem_of_chunks
#print axioms forall_fin_pair_of_chunks
end SparseMonotiles.Contact
