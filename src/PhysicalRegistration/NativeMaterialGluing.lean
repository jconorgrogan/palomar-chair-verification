module

public import PhysicalRegistration.MaterialCovariance
public import PhysicalRegistration.NativeMaterialAvoidance

@[expose] public section

/-!
# Global gluing of literal tube replacements

The proofs below derive coverage and disjoint actual interiors from elementary
carrier geometry and local piece partitions. There is no body-tiling or
material-gluing certificate among the inputs. Only finitely many frontiers
from the two tiles under comparison are avoided; no global local-finiteness or
Baire hypothesis is used.
-/
namespace PhysicalRegistration.NativeMaterialGluing
open Set
noncomputable section

variable {X ι κ : Type*} [TopologicalSpace X]

/-- The literal carrier-minus-open-tubes plus closed-piece assembly. -/
def assemble (C : Set X) (T P : κ → Set X) : Set X :=
  (C \ ⋃ u, interior (T u)) ∪ ⋃ u, P u

/-- Local pair partitions fill every point removed from a covering carrier. -/
theorem assemble_covers (C : ι → Set X) (T P : ι → κ → Set X)
    (hC : ∀ x, ∃ i, x ∈ C i)
    (hfill : ∀ i u, ∃ j v, T i u ⊆ P i u ∪ P j v) :
    ∀ x, ∃ i, x ∈ assemble (C i) (T i) (P i) := by
  classical
  intro x
  obtain ⟨i, hxi⟩ := hC x
  by_cases hxT : ∃ u, x ∈ interior (T i u)
  · obtain ⟨u, hxu⟩ := hxT
    obtain ⟨j, v, hfill⟩ := hfill i u
    rcases hfill (interior_subset hxu) with hi | hj
    · exact ⟨i, Or.inr (mem_iUnion.mpr ⟨u, hi⟩)⟩
    · exact ⟨j, Or.inr (mem_iUnion.mpr ⟨v, hj⟩)⟩
  · exact ⟨i, Or.inl ⟨hxi, fun h => hxT (mem_iUnion.mp h)⟩⟩

/-- The carrier or one of its finitely many closed replacement pieces. -/
def carrierOrPiece (C : Set X) (P : κ → Set X) : Option κ → Set X
  | none => C
  | some u => P u

/-- Finite closed-frontier avoidance turns a hypothetical open body overlap
into actual interiors of the constituent carrier/piece sets. The four
assembly cases then contradict carrier disjointness, tube isolation, or the
local complementary-piece partition. -/
theorem assemble_interiors_disjoint [Finite κ]
    (C : ι → Set X) (T P : ι → κ → Set X)
    (hCclosed : ∀ i, IsClosed (C i)) (hPclosed : ∀ i u, IsClosed (P i u))
    (hPsub : ∀ i u, P i u ⊆ T i u)
    (hCdisjoint : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hisolation : ∀ i j, i ≠ j → ∀ u,
      Disjoint (T i u) (C j) ∨ ∃ v, T i u = T j v)
    (hpieces : ∀ i j, i ≠ j → ∀ u v,
      Disjoint (T i u) (T j v) ∨ Disjoint (interior (P i u)) (interior (P j v))) :
    Pairwise fun i j =>
      Disjoint (interior (assemble (C i) (T i) (P i)))
        (interior (assemble (C j) (T j) (P j))) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  let S : Bool × Option κ → Set X := fun z =>
    if z.1 then carrierOrPiece (C i) (P i) z.2 else carrierOrPiece (C j) (P j) z.2
  have hS : ∀ z, IsClosed (S z) := by
    rintro ⟨b,u⟩
    cases b <;> cases u <;> first | exact hCclosed _ | exact hPclosed _ _
  obtain ⟨y, hy, havoid⟩ := exists_mem_open_avoid_closed
    (fun z => frontier (S z)) (fun _ => isClosed_frontier)
    (fun z => interior_frontier (hS z))
    (interior (assemble (C i) (T i) (P i)) ∩ interior (assemble (C j) (T j) (P j)))
    (isOpen_interior.inter isOpen_interior) ⟨x, hxi, hxj⟩
  have hCi (h : y ∈ C i) : y ∈ interior (C i) :=
    (mem_interior_iff_notMem_frontier h).mpr (havoid (true, none))
  have hCj (h : y ∈ C j) : y ∈ interior (C j) :=
    (mem_interior_iff_notMem_frontier h).mpr (havoid (false, none))
  have hPi (u : κ) (h : y ∈ P i u) : y ∈ interior (P i u) :=
    (mem_interior_iff_notMem_frontier h).mpr (havoid (true, some u))
  have hPj (v : κ) (h : y ∈ P j v) : y ∈ interior (P j v) :=
    (mem_interior_iff_notMem_frontier h).mpr (havoid (false, some v))
  have hbi := interior_subset hy.1
  have hbj := interior_subset hy.2
  rcases hbi with hci | hpi <;> rcases hbj with hcj | hpj
  · exact Set.disjoint_left.mp (hCdisjoint hij) (hCi hci.1) (hCj hcj.1)
  · obtain ⟨v, hpv⟩ := mem_iUnion.mp hpj
    rcases hisolation j i hij.symm v with hd | ⟨u, htu⟩
    · exact Set.disjoint_left.mp hd (hPsub j v hpv) hci.1
    · have hi : y ∈ interior (T i u) := htu ▸ interior_mono (hPsub j v) (hPj v hpv)
      exact hci.2 (mem_iUnion.mpr ⟨u, hi⟩)
  · obtain ⟨u, hpu⟩ := mem_iUnion.mp hpi
    rcases hisolation i j hij u with hd | ⟨v, htv⟩
    · exact Set.disjoint_left.mp hd (hPsub i u hpu) hcj.1
    · have hj : y ∈ interior (T j v) := htv ▸ interior_mono (hPsub i u) (hPi u hpu)
      exact hcj.2 (mem_iUnion.mpr ⟨v, hj⟩)
  · obtain ⟨u, hpu⟩ := mem_iUnion.mp hpi
    obtain ⟨v, hpv⟩ := mem_iUnion.mp hpj
    rcases hpieces i j hij u v with hd | hd
    · exact Set.disjoint_left.mp hd (hPsub i u hpu) (hPsub j v hpv)
    · exact Set.disjoint_left.mp hd (hPi u hpu) (hPj v hpv)

end
end PhysicalRegistration.NativeMaterialGluing

namespace PhysicalRegistration.NativeChair
open Set
open PhysicalRegistration.NativeMaterialGluing
noncomputable section

/-- Isometric placement commutes with the literal finite tube assembly. -/
theorem placedBody_eq_assemble {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (f : Space m ≃ᵢ Space m) :
    placedBody a f = assemble (f '' carrier m)
      (fun u => f '' closedTube J u) (fun u => f '' replacementPiece a u) := by
  unfold placedBody body assemble
  rw [Set.image_union, Set.image_sdiff f.injective, Set.image_iUnion, Set.image_iUnion]
  have hi (u : Site m) : f '' interior (closedTube J u) = interior (f '' closedTube J u) :=
    f.toHomeomorph.image_interior _
  simp_rw [hi]


/-- Relative-coordinate images bind exactly to the two original placements. -/
theorem placed_relative_image {m : ℕ} (f g : Space m ≃ᵢ Space m) (S : Set (Space m)) :
    f '' (relativePlacement f g '' S) = g '' S := by
  rw [Set.image_image]
  have he : (fun x => f (relativePlacement f g x)) = g := by
    funext x
    exact f.apply_symm_apply (g x)
  rw [he]

/-- A matched native site pair has one literal common world-coordinate tube. -/
theorem SiteTransport.placed_closedTube {m : ℕ}
    {f g : Space m ≃ᵢ Space m} {u v : Site m}
    (h : SiteTransport (relativePlacement f g) u v) (J : ℕ) :
    f '' closedTube J u = g '' closedTube J v := by
  have hp := congrArg (Set.image f) (h.image_closedTube J)
  rw [placed_relative_image] at hp
  exact hp.symm

/-- Actual paired material pieces cover their common tube in world coordinates. -/
theorem SiteTransport.placed_replacementPiece_union {m J : ℕ} [NeZero m]
    {f g : Space m ≃ᵢ Space m} {u v : Site m}
    (h : SiteTransport (relativePlacement f g) u v)
    (a : Coefficients m J) (hc : a.value v = -a.value u) :
    (f '' replacementPiece a u) ∪ (g '' replacementPiece a v) = f '' closedTube J u := by
  have hp := congrArg (Set.image f) (h.replacementPiece_union a hc)
  rw [Set.image_union, placed_relative_image] at hp
  exact hp

/-- Their actual world-coordinate interiors remain disjoint under placement. -/
theorem SiteTransport.placed_replacementPiece_interiors_disjoint
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {f g : Space m ≃ᵢ Space m} {u v : Site m}
    (h : SiteTransport (relativePlacement f g) u v)
    (a : Coefficients m J) (hc : a.value v = -a.value u) :
    Disjoint (interior (f '' replacementPiece a u)) (interior (g '' replacementPiece a v)) := by
  have hd := (Set.disjoint_image_iff f.injective).mpr
    (h.replacementPiece_interiors_disjoint hm a hc)
  have hi (S : Set (Space m)) : f '' interior S = interior (f '' S) :=
    f.toHomeomorph.image_interior S
  rw [hi, hi, placed_relative_image] at hd
  exact hd

/-- Actual placed body coverage and nonoverlap follow from the carrier world,
paired tube geometry, and local complementary replacement pieces. -/
theorem physicalTiling_of_tube_partitions
    {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hcover : ∀ x, ∃ i, x ∈ f i '' carrier m)
    (hcarrier : Pairwise fun i j =>
      Disjoint (interior (f i '' carrier m)) (interior (f j '' carrier m)))
    (hfill : ∀ i u, ∃ j v, f i '' closedTube J u ⊆
      (f i '' replacementPiece a u) ∪ (f j '' replacementPiece a v))
    (hisolation : ∀ i j, i ≠ j → ∀ u,
      Disjoint (f i '' closedTube J u) (f j '' carrier m) ∨
        ∃ v, f i '' closedTube J u = f j '' closedTube J v)
    (hpieces : ∀ i j, i ≠ j → ∀ u v,
      Disjoint (f i '' closedTube J u) (f j '' closedTube J v) ∨
        Disjoint (interior (f i '' replacementPiece a u))
          (interior (f j '' replacementPiece a v))) : PhysicalTiling a f := by
  have hCclosed (i : ι) : IsClosed (f i '' carrier m) :=
    (f i).toHomeomorph.isClosedMap _ (carrier_isClosed m)
  have hPclosed (i : ι) (u : Site m) : IsClosed (f i '' replacementPiece a u) :=
    (f i).toHomeomorph.isClosedMap _ ((closedTube_isClosed J u).inter (siteHypograph_isClosed a u))
  have hPsub (i : ι) (u : Site m) : f i '' replacementPiece a u ⊆ f i '' closedTube J u :=
    Set.image_mono inter_subset_left
  constructor
  · simpa only [placedBody_eq_assemble] using assemble_interiors_disjoint
      (fun i => f i '' carrier m) (fun i u => f i '' closedTube J u)
      (fun i u => f i '' replacementPiece a u) hCclosed hPclosed hPsub hcarrier hisolation hpieces
  · simpa only [placedBody_eq_assemble] using assemble_covers
      (fun i => f i '' carrier m) (fun i u => f i '' closedTube J u)
      (fun i u => f i '' replacementPiece a u) hcover hfill


/-- A geometric matched-tube interface: every tube is paired, and distinct
world tubes either miss or arise from an actual complete native site matching
with opposite coefficients. The material gluing conclusion is derived. -/
theorem physicalTiling_of_matched_tubes
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hcover : ∀ x, ∃ i, x ∈ f i '' carrier m)
    (hcarrier : Pairwise fun i j =>
      Disjoint (interior (f i '' carrier m)) (interior (f j '' carrier m)))
    (hmatch : ∀ i u, ∃ j v, SiteTransport (relativePlacement (f i) (f j)) u v ∧
      a.value v = -a.value u)
    (hisolation : ∀ i j, i ≠ j → ∀ u,
      Disjoint (f i '' closedTube J u) (f j '' carrier m) ∨
        ∃ v, f i '' closedTube J u = f j '' closedTube J v)
    (htubes : ∀ i j, i ≠ j → ∀ u v,
      Disjoint (f i '' closedTube J u) (f j '' closedTube J v) ∨
        (SiteTransport (relativePlacement (f i) (f j)) u v ∧ a.value v = -a.value u)) :
    PhysicalTiling a f := by
  apply physicalTiling_of_tube_partitions a f hcover hcarrier
  · intro i u
    obtain ⟨j, v, ht, hc⟩ := hmatch i u
    exact ⟨j, v, (ht.placed_replacementPiece_union a hc).symm.subset⟩
  · exact hisolation
  · intro i j hij u v
    rcases htubes i j hij u v with hd | ⟨ht, hc⟩
    · exact Or.inl hd
    · exact Or.inr (ht.placed_replacementPiece_interiors_disjoint hm a hc)

#print axioms placedBody_eq_assemble
#print axioms SiteTransport.placed_replacementPiece_union
#print axioms SiteTransport.placed_replacementPiece_interiors_disjoint
#print axioms physicalTiling_of_matched_tubes
#print axioms physicalTiling_of_tube_partitions
end
end PhysicalRegistration.NativeChair
