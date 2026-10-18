module

public import SpectreFinite.WindowTranslation

@[expose] public section


/-!
Sound finite overlap-consistency pruning for relative-position windows.
The pruning algorithm is executable and its completeness invariant is proved
for any specified finite domain and list of offsets. No particular supplied
patch file is assumed exhaustive, and no global field or physical tiling is
asserted to exist.
-/
namespace SpectreFinite.HexSearch

/-- `q` is centered at offset `delta` relative to `p`. They must agree only
where their relative positions represent the same absolute position. -/
def overlap (p q : Patch) (delta : Position) : Bool :=
  p.all (fun a => q.all (fun b =>
    decide (a.1 = addPos delta b.1 → a.2 = b.2)))

theorem overlap_iff (p q : Patch) (delta : Position) :
    overlap p q delta = true ↔
      ∀ a ∈ p, ∀ b ∈ q, a.1 = addPos delta b.1 → a.2 = b.2 := by
  simp only [overlap, List.all_eq_true, decide_eq_true_eq]

/-- Any two windows of the same field agree on their actual overlap.
This assertion needs no matching hypothesis and permits different domains. -/
theorem extract_overlap (f : Position → State) (center delta : Position)
    (domain₁ domain₂ : List Position) :
    overlap (extract f center domain₁)
      (extract f (addPos center delta) domain₂) delta = true := by
  apply (overlap_iff _ _ _).mpr
  intro a ha b hb hxy
  obtain ⟨haDomain, haState⟩ := (mem_extract_iff f center domain₁ a.1 a.2).mp ha
  obtain ⟨hbDomain, hbState⟩ :=
    (mem_extract_iff f (addPos center delta) domain₂ b.1 b.2).mp hb
  rw [haState, hbState, hxy, addPos_assoc]

/-- Keep a patch only if each requested offset has at least one compatible
supporting patch in the current family. All tests use the same input family. -/
def reduce (offsets : List Position) (family : List Patch) : List Patch :=
  family.filter (fun p =>
    offsets.all (fun delta => family.any (fun q => overlap p q delta)))

theorem mem_reduce_iff (offsets : List Position) (family : List Patch) (p : Patch) :
    p ∈ reduce offsets family ↔
      p ∈ family ∧ ∀ delta ∈ offsets, ∃ q ∈ family, overlap p q delta = true := by
  simp [reduce, List.mem_filter, List.all_eq_true, List.any_eq_true]

theorem mem_of_mem_reduce (offsets : List Position) (family : List Patch) (p : Patch)
    (hp : p ∈ reduce offsets family) : p ∈ family :=
  ((mem_reduce_iff offsets family p).mp hp).1

/-- Every window occurring in this particular field is represented. This is
a proved invariant when initialized by `assignments`, not a file axiom. -/
def OccurrenceComplete (f : Position → State) (domain : List Position)
    (family : List Patch) : Prop :=
  ∀ center : Position, extract f center domain ∈ family

/-- Pruning cannot discard any occurring window: the actual neighboring
window supplies the required witness at every requested offset. -/
theorem occurrenceComplete_reduce (f : Position → State) (domain : List Position)
    (family : List Patch) (offsets : List Position)
    (hf : OccurrenceComplete f domain family) :
    OccurrenceComplete f domain (reduce offsets family) := by
  intro center
  apply (mem_reduce_iff offsets family _).mpr
  refine ⟨hf center, ?_⟩
  intro delta hdelta
  exact ⟨extract f (addPos center delta) domain, hf (addPos center delta),
    extract_overlap f center delta domain domain⟩

def reduceIter (offsets : List Position) : Nat → List Patch → List Patch
  | 0, family => family
  | n + 1, family => reduce offsets (reduceIter offsets n family)

theorem occurrenceComplete_reduceIter (f : Position → State) (domain : List Position)
    (family : List Patch) (offsets : List Position)
    (hf : OccurrenceComplete f domain family) (n : Nat) :
    OccurrenceComplete f domain (reduceIter offsets n family) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact occurrenceComplete_reduce f domain _ offsets ih

theorem mem_of_mem_reduceIter (offsets : List Position) (family : List Patch)
    (n : Nat) (p : Patch) (hp : p ∈ reduceIter offsets n family) : p ∈ family := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ih (mem_of_mem_reduce offsets _ p hp)

theorem occurrenceComplete_assignments (f : Position → State) (hf : GloballyLegal f)
    (domain : List Position) (hn : domain.Nodup) :
    OccurrenceComplete f domain (assignments domain) :=
  fun center => extract_enumerated f hf center domain hn

/-- Main invariant: every window of any globally matching discrete field
survives any finite number of the explicitly defined pruning rounds. -/
theorem extract_mem_pruned_assignments (f : Position → State) (hf : GloballyLegal f)
    (domain : List Position) (hn : domain.Nodup) (offsets : List Position)
    (n : Nat) (center : Position) :
    extract f center domain ∈ reduceIter offsets n (assignments domain) :=
  occurrenceComplete_reduceIter f domain (assignments domain) offsets
    (occurrenceComplete_assignments f hf domain hn) n center

/-- The fixed 91-position radius-five domain inherits the pruning invariant.
No evaluation or classification of that search is claimed here. -/
theorem radiusFive_extract_mem_pruned_assignments (f : Position → State)
    (hf : GloballyLegal f) (offsets : List Position) (n : Nat) (center : Position) :
    extract f center (hexRegion 5) ∈ reduceIter offsets n (assignments (hexRegion 5)) :=
  extract_mem_pruned_assignments f hf (hexRegion 5) hexRegion_five_nodup offsets n center

/-- A finite certificate can transfer a property to actual field windows,
provided its exact family equality is proved separately. -/
theorem property_of_pruning_certificate (domain : List Position) (hn : domain.Nodup)
    (offsets : List Position) (n : Nat) (certified : List Patch)
    (hcertificate : reduceIter offsets n (assignments domain) = certified)
    (P : Patch → Prop) (hP : ∀ p ∈ certified, P p)
    (f : Position → State) (hf : GloballyLegal f) (center : Position) :
    P (extract f center domain) := by
  apply hP
  rw [← hcertificate]
  exact extract_mem_pruned_assignments f hf domain hn offsets n center

#print axioms overlap_iff
#print axioms extract_overlap
#print axioms mem_reduce_iff
#print axioms mem_of_mem_reduce
#print axioms occurrenceComplete_reduce
#print axioms occurrenceComplete_reduceIter
#print axioms mem_of_mem_reduceIter
#print axioms occurrenceComplete_assignments
#print axioms extract_mem_pruned_assignments
#print axioms radiusFive_extract_mem_pruned_assignments
#print axioms property_of_pruning_certificate
end SpectreFinite.HexSearch
