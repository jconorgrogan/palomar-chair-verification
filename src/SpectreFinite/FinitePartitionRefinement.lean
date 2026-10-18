module

public import SpectreFinite.AxialTranslationWords

@[expose] public section


/-!
Finite-list refinement for a later geometric hierarchy. Distinct exact owner
fibers give genuine finite blocks, and local edge expansions give a boundary
cover with the factor six. Iteration derives the quantitative bounds from
these local hypotheses; it does not assume the desired growth estimates.

The owner maps, exact fiber lists, inter-level neighbor law, and concrete
edge expansions must still be constructed geometrically at every level.
This module does not assert a hierarchy, period intersection law, physical
tiling existence, or aperiodicity. All transitive external imports are Init.
-/
namespace SpectreFinite.HexSearch.FinitePartitionRefinement
open FiniteBoundaryEstimate

/-- Flatten concrete fibers, retaining their actual cells. -/
def refine {α : Type u} {β : Type v} (fibers : α → List β) (A : List α) : List β :=
  A.flatMap fibers

theorem mem_refine {α : Type u} {β : Type v}
    (fibers : α → List β) (A : List α) (x : β) :
    x ∈ refine fibers A ↔ ∃ a ∈ A, x ∈ fibers a := List.mem_flatMap

theorem refine_nodup {α : Type u} {β : Type v}
    (fibers : α → List β) (A : List α) (hA : A.Nodup)
    (hf : ∀ a ∈ A, (fibers a).Nodup)
    (hd : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ x ∈ fibers a, x ∉ fibers b) :
    (refine fibers A).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨hf, List.Pairwise.imp_of_mem ?_ hA⟩
  intro a b ha hb hab x hx y hy hxy
  exact hd a ha b hb hab x hx (hxy ▸ hy)

theorem refine_length_lower {α : Type u} {β : Type v}
    (fibers : α → List β) (A : List α) (k : Nat)
    (hf : ∀ a ∈ A, k ≤ (fibers a).length) :
    k*A.length ≤ (refine fibers A).length := by
  induction A with
  | nil => simp [refine]
  | cons a A ih =>
    have ha := hf a (by simp)
    have ht := ih (fun b hb => hf b (by simp [hb]))
    simpa only [refine,List.flatMap_cons,List.length_append,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_comm] using Nat.add_le_add ha ht

theorem refine_length_upper {α : Type u} {β : Type v}
    (fibers : α → List β) (A : List α) (k : Nat)
    (hf : ∀ a ∈ A, (fibers a).length ≤ k) :
    (refine fibers A).length ≤ k*A.length := by
  induction A with
  | nil => simp [refine]
  | cons a A ih =>
    have ha := hf a (by simp)
    have ht := ih (fun b hb => hf b (by simp [hb]))
    simpa only [refine,List.flatMap_cons,List.length_append,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_comm] using Nat.add_le_add ha ht

theorem refine_length_bounds (fibers : Position → List Position) (A : List Position)
    (hf : ∀ a ∈ A, 7 ≤ (fibers a).length ∧ (fibers a).length ≤ 8) :
    7*A.length ≤ (refine fibers A).length ∧ (refine fibers A).length ≤ 8*A.length :=
  ⟨refine_length_lower fibers A 7 (fun a ha => (hf a ha).1),
    refine_length_upper fibers A 8 (fun a ha => (hf a ha).2)⟩

/-- An exact owner fiber makes flattened membership an owner test. -/
theorem mem_refine_iff_owner {α : Type u} {β : Type v}
    (owner : β → α) (fibers : α → List β)
    (hf : ∀ a x, x ∈ fibers a ↔ owner x = a) (A : List α) (x : β) :
    x ∈ refine fibers A ↔ owner x ∈ A := by
  rw [mem_refine]
  constructor
  · rintro ⟨a,ha,hx⟩
    exact (hf a x).mp hx ▸ ha
  · intro hx
    exact ⟨owner x,hx,(hf (owner x) x).mpr rfl⟩

theorem exact_fibers_disjoint {α : Type u} {β : Type v}
    (owner : β → α) (fibers : α → List β)
    (hf : ∀ a x, x ∈ fibers a ↔ owner x = a)
    (a b : α) (hab : a ≠ b) (x : β) (hx : x ∈ fibers a) : x ∉ fibers b := by
  intro hy
  exact hab (((hf a x).mp hx).symm.trans ((hf b x).mp hy))

theorem refine_nodup_of_owner {α : Type u} {β : Type v}
    (owner : β → α) (fibers : α → List β)
    (hf : ∀ a x, x ∈ fibers a ↔ owner x = a)
    (A : List α) (hA : A.Nodup) (hn : ∀ a ∈ A, (fibers a).Nodup) :
    (refine fibers A).Nodup :=
  refine_nodup fibers A hA hn
    (fun a _ b _ hab x hx => exact_fibers_disjoint owner fibers hf a b hab x hx)

/-- Level-dependent refinement, with no closure or growth hidden in a record. -/
def iterate {α : Type u} (fibers : Nat → α → List α) (seed : List α) : Nat → List α
  | 0 => seed
  | n+1 => refine (fibers n) (iterate fibers seed n)

theorem iterate_nodup {α : Type u} (fibers : Nat → α → List α) (seed : List α)
    (hs : seed.Nodup) (hn : ∀ n a, (fibers n a).Nodup)
    (hd : ∀ n a b, a ≠ b → ∀ x ∈ fibers n a, x ∉ fibers n b) :
    ∀ n, (iterate fibers seed n).Nodup := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact refine_nodup (fibers n) _ ih (fun a _ => hn n a)
      (fun a _ b _ => hd n a b)

theorem iterate_length_lower {α : Type u} (fibers : Nat → α → List α)
    (seed : List α) (k : Nat) (hf : ∀ n a, k ≤ (fibers n a).length) :
    ∀ n, k^n*seed.length ≤ (iterate fibers seed n).length := by
  intro n
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    calc
      k^(n+1)*seed.length = k*(k^n*seed.length) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ k*(iterate fibers seed n).length := Nat.mul_le_mul_left k ih
      _ ≤ (iterate fibers seed (n+1)).length :=
        refine_length_lower (fibers n) _ k (fun a _ => hf n a)

theorem iterate_length_upper {α : Type u} (fibers : Nat → α → List α)
    (seed : List α) (k : Nat) (hf : ∀ n a, (fibers n a).length ≤ k) :
    ∀ n, (iterate fibers seed n).length ≤ seed.length*k^n := by
  intro n
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    calc
      (iterate fibers seed (n+1)).length ≤ k*(iterate fibers seed n).length :=
        refine_length_upper (fibers n) _ k (fun a _ => hf n a)
      _ ≤ k*(seed.length*k^n) := Nat.mul_le_mul_left k ih
      _ = seed.length*k^(n+1) := by rw [Nat.pow_succ]; ac_rfl

abbrev Edge := Position × Fin 6

def hexStep (x : Position) (d : Fin 6) : Position := addPos x (direction d)

def Exposed (step : Position → Fin 6 → Position) (A : List Position) (e : Edge) : Prop :=
  e.1 ∈ A ∧ step e.1 e.2 ∉ A

def CoversBoundary (step : Position → Fin 6 → Position) (A : List Position)
    (E : List Edge) : Prop := ∀ e, Exposed step A e → e ∈ E

theorem expand_edges_length_le (expand : Edge → List Edge) (E : List Edge)
    (he : ∀ e ∈ E, (expand e).length ≤ 6) :
    (refine expand E).length ≤ 6*E.length := refine_length_upper expand E 6 he

/-- All six oriented edges at one cell form a concrete initial cover. -/
def cellEdges (x : Position) : List Edge := (List.finRange 6).map (fun d => (x,d))

theorem cellEdges_length (x : Position) : (cellEdges x).length = 6 := by
  simp [cellEdges]

theorem cellEdges_covers (step : Position → Fin 6 → Position) (x : Position) :
    CoversBoundary step [x] (cellEdges x) := by
  intro e he
  have hx : e.1 = x := List.mem_singleton.mp he.1
  apply List.mem_map.mpr
  exact ⟨e.2,List.mem_finRange _,Prod.ext hx.symm rfl⟩

/-- Transport a cover using a concrete coarse-edge witness for each fine
exposed edge. This form plugs directly into geometric boundary refinements. -/
theorem refine_boundary_covers_of_witness
    (coarseStep fineStep : Position → Fin 6 → Position)
    (fibers : Position → List Position) (expand : Edge → List Edge)
    (A : List Position) (E : List Edge)
    (hw : ∀ b, Exposed fineStep (refine fibers A) b →
      ∃ e, Exposed coarseStep A e ∧ b ∈ expand e)
    (he : CoversBoundary coarseStep A E) :
    CoversBoundary fineStep (refine fibers A) (refine expand E) := by
  intro b hb
  obtain ⟨e,hex,hem⟩ := hw b hb
  exact (mem_refine expand E b).mpr ⟨e,he e hex,hem⟩

/-- A local crossing witness is enough to transport a coarse boundary cover.
The expansion lists are concrete inputs; the crossing witness records both
neighbor preservation and membership in the corresponding expansion. -/
theorem refine_boundary_covers
    (coarseStep fineStep : Position → Fin 6 → Position)
    (owner : Position → Position) (fibers : Position → List Position)
    (expand : Edge → List Edge)
    (hf : ∀ a x, x ∈ fibers a ↔ owner x = a)
    (hc : ∀ x d, owner (fineStep x d) ≠ owner x →
      ∃ s : Fin 6, owner (fineStep x d) = coarseStep (owner x) s ∧
        (x,d) ∈ expand (owner x,s))
    (A : List Position) (E : List Edge) (he : CoversBoundary coarseStep A E) :
    CoversBoundary fineStep (refine fibers A) (refine expand E) := by
  intro e hex
  obtain ⟨x,d⟩ := e
  have hin : owner x ∈ A := (mem_refine_iff_owner owner fibers hf A x).mp hex.1
  have hout : owner (fineStep x d) ∉ A := by
    intro hm
    exact hex.2 ((mem_refine_iff_owner owner fibers hf A _).mpr hm)
  have hne : owner (fineStep x d) ≠ owner x := by
    intro heq
    exact hout (heq ▸ hin)
  obtain ⟨s,hs,hmem⟩ := hc x d hne
  apply (mem_refine expand E (x,d)).mpr
  refine ⟨(owner x,s),he (owner x,s) ⟨hin,?_⟩,hmem⟩
  exact hs ▸ hout

theorem iterate_boundary_covers
    (step : Nat → Position → Fin 6 → Position)
    (owner : Nat → Position → Position) (fibers : Nat → Position → List Position)
    (expand : Nat → Edge → List Edge)
    (hf : ∀ n a x, x ∈ fibers n a ↔ owner n x = a)
    (hc : ∀ n x d, owner n (step (n+1) x d) ≠ owner n x →
      ∃ s : Fin 6, owner n (step (n+1) x d) = step n (owner n x) s ∧
        (x,d) ∈ expand n (owner n x,s))
    (A : List Position) (E : List Edge) (he : CoversBoundary (step 0) A E) :
    ∀ n, CoversBoundary (step n) (iterate fibers A n) (iterate expand E n) := by
  intro n
  induction n with
  | zero => exact he
  | succ n ih =>
    exact refine_boundary_covers (step n) (step (n+1)) (owner n) (fibers n)
      (expand n) (hf n) (hc n) _ _ ih

theorem iterate_nodup_of_owner
    (owner : Nat → Position → Position) (fibers : Nat → Position → List Position)
    (hf : ∀ n a x, x ∈ fibers n a ↔ owner n x = a)
    (hn : ∀ n a, (fibers n a).Nodup) (A : List Position) (ha : A.Nodup) :
    ∀ n, (iterate fibers A n).Nodup :=
  iterate_nodup fibers A ha hn
    (fun n a b hab x hx => exact_fibers_disjoint (owner n) (fibers n) (hf n) a b hab x hx)

theorem iterate_singleton_area_lower
    (fibers : Nat → Position → List Position)
    (hf : ∀ n a, 7 ≤ (fibers n a).length) (x : Position) (n : Nat) :
    7^n ≤ (iterate fibers [x] n).length := by
  simpa using iterate_length_lower fibers [x] 7 hf n

theorem iterate_boundary_length_upper (expand : Nat → Edge → List Edge)
    (he : ∀ n e, (expand n e).length ≤ 6) (E : List Edge) (C : Nat)
    (hE : E.length ≤ C) (n : Nat) :
    (iterate expand E n).length ≤ C*6^n :=
  Nat.le_trans (iterate_length_upper expand E 6 he n) (Nat.mul_le_mul_right _ hE)

/-- Repeated endpoints are allowed: their list length remains bounded by the
edge count, which is all the finite translation estimate requires. -/
def boundarySources (E : List Edge) : List Position := E.map Prod.fst

theorem boundarySources_length (E : List Edge) : (boundarySources E).length = E.length :=
  List.length_map _

theorem escape_subset_boundarySources (A : List Position) (E : List Edge)
    (he : CoversBoundary hexStep A E) (s : Position) (hs : s ∈ primitiveSteps) :
    escape A s ⊆ boundarySources E := by
  obtain ⟨d,hd⟩ := primitiveSteps_directions s hs
  intro x hx
  obtain ⟨hin,hout⟩ := (mem_escape A s x).mp hx
  have hex : Exposed hexStep A (x,d) := by
    simpa only [Exposed,hexStep,hd] using And.intro hin hout
  exact List.mem_map.mpr ⟨(x,d),he (x,d) hex,rfl⟩

/-- The finite inputs needed by the existing boundary-period estimate, derived
from local fibers and local edge crossing data. No period or global legal
hierarchy premise is packaged or asserted here. The upper fiber bound eight
is available separately in `refine_length_bounds`; this result needs only
its lower bound seven. -/
theorem iterate_singleton_estimates
    (owner : Nat → Position → Position) (fibers : Nat → Position → List Position)
    (expand : Nat → Edge → List Edge)
    (hf : ∀ n a x, x ∈ fibers n a ↔ owner n x = a)
    (hn : ∀ n a, (fibers n a).Nodup)
    (ha : ∀ n a, 7 ≤ (fibers n a).length)
    (he : ∀ n e, (expand n e).length ≤ 6)
    (hc : ∀ n x d, owner n (hexStep x d) ≠ owner n x →
      ∃ s : Fin 6, owner n (hexStep x d) = hexStep (owner n x) s ∧
        (x,d) ∈ expand n (owner n x,s))
    (x : Position) (n : Nat) :
    (iterate fibers [x] n).Nodup ∧
    7^n ≤ (iterate fibers [x] n).length ∧
    (boundarySources (iterate expand (cellEdges x) n)).length ≤ 6*6^n ∧
    (∀ s ∈ primitiveSteps,
      escape (iterate fibers [x] n) s ⊆ boundarySources (iterate expand (cellEdges x) n)) := by
  refine ⟨iterate_nodup_of_owner owner fibers hf hn [x] (by simp) n,
    iterate_singleton_area_lower fibers ha x n,?_,?_⟩
  · rw [boundarySources_length]
    exact iterate_boundary_length_upper expand he (cellEdges x) 6
      (Nat.le_of_eq (cellEdges_length x)) n
  · have hcov := iterate_boundary_covers (fun _ => hexStep) owner fibers expand hf hc
      [x] (cellEdges x) (cellEdges_covers hexStep x) n
    exact fun s hs => escape_subset_boundarySources _ _ hcov s hs

end SpectreFinite.HexSearch.FinitePartitionRefinement
