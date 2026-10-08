module

public import SparseMonotiles.IncidentTileLocalization
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Continuing a physical companion across a connected generic face

The input is the pointwise local halfspace conclusion of K1. The assignment of
physical tiles is not assumed locally constant: a set germ persists throughout
an open neighborhood, and two physical tiles with the same full-dimensional
germ would have overlapping ambient interiors. Connectedness then identifies
one tile, and closedness includes the entire closure of the generic face.

The local-finiteness and finite-sector arguments are needed to establish the
pointwise input; continuation itself requires only disjoint tile interiors.
The intrinsic version accepts exactly the connectedness and density outputs
of the generic-face construction, without any face-to-face premise.
-/
namespace SparseMonotiles

open Set Filter
open scoped Topology

namespace LocalSetEq

variable {X : Type*} [TopologicalSpace X]

/-- Ambient interior is local, as is closure. -/
private theorem companion_interior {p : X} {S H : Set X} (h : LocalSetEq p S H) :
    LocalSetEq p (_root_.interior S) (_root_.interior H) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

/-- A germ valid at one point remains valid at every sufficiently nearby point. -/
theorem eventually {p : X} {S H : Set X} (h : LocalSetEq p S H) :
    ∀ᶠ y in 𝓝 p, LocalSetEq y S H := by
  obtain ⟨U, hU, hpU, heq⟩ := h.exists_open
  exact Filter.Eventually.mono (hU.mem_nhds hpU) fun y hy => LocalSetEq.of_open hU hy heq

/-- Two copies of the same full-dimensional germ cannot have disjoint interiors.
The closure-interior hypothesis includes boundary points of a genuine halfspace. -/
theorem not_disjoint_interiors {p : X} {A B H : Set X}
    (hA : LocalSetEq p A H) (hB : LocalSetEq p B H)
    (hp : p ∈ _root_.closure (_root_.interior H)) :
    ¬ Disjoint (_root_.interior A) (_root_.interior B) := by
  intro hd
  have hh := (hA.companion_interior.inter hB.companion_interior).closure.mem_iff
  have hp' : p ∈ _root_.closure (_root_.interior H ∩ _root_.interior H) := by
    simpa only [inter_self] using hp
  have hab := hh.mpr hp'
  rw [Set.disjoint_iff_inter_eq_empty.mp hd, closure_empty] at hab
  exact hab

end LocalSetEq

namespace IsTiling

variable {d : ℕ} {T : Set (Point d)} {tiles : Set (Set (Point d))}

/-- The same genuine local halfspace determines at most one physical tile. -/
theorem eq_of_common_local_germ (ht : IsTiling T tiles)
    {p : Point d} {A B H : Set (Point d)}
    (hA : A ∈ tiles) (hB : B ∈ tiles)
    (hAlocal : LocalSetEq p A H) (hBlocal : LocalSetEq p B H)
    (hp : p ∈ closure (interior H)) : A = B := by
  by_contra hne
  exact hAlocal.not_disjoint_interiors hBlocal hp (ht.2.2 A hA B hB hne)

/-- Any pointwise choice of physical halfspace companions is locally constant.
No local constancy or continuity of the chosen tiles is an input. -/
theorem companionAssignment_isLocallyConstant (ht : IsTiling T tiles)
    {X : Type*} [TopologicalSpace X] (p : X → Point d) (hp : Continuous p)
    (H : Set (Point d)) (B : X → Set (Point d))
    (hB : ∀ x, B x ∈ tiles)
    (hlocal : ∀ x, LocalSetEq (p x) (B x) H)
    (hregular : ∀ x, p x ∈ closure (interior H)) :
    IsLocallyConstant B := by
  apply (IsLocallyConstant.iff_eventually_eq B).mpr
  intro x
  filter_upwards [hp.continuousAt (hlocal x).eventually] with y hy
  exact ht.eq_of_common_local_germ (hB y) (hB x) (hlocal y) hy (hregular y)

/-- Pointwise halfspace companions on a connected ambient generic set select one
physical tile. The tile contains the whole closed face whenever that face is
contained in the closure of the generic set. -/
theorem exists_unique_companion_on_connected_set (ht : IsTiling T tiles)
    (hT : IsCompact T) {G H : Set (Point d)} (hG : IsConnected G)
    (hregular : G ⊆ closure (interior H))
    (hex : ∀ x ∈ G, ∃ B ∈ incidentTiles tiles x, LocalSetEq x B H) :
    ∃! B : Set (Point d), B ∈ tiles ∧
      (∀ x ∈ G, LocalSetEq x B H) ∧ closure G ⊆ B := by
  classical
  choose B hB hlocal using fun x : G => hex x x.property
  have hconst := ht.companionAssignment_isLocallyConstant
    (fun x : G => (x : Point d)) continuous_subtype_val H B
    (fun x => (hB x).1) hlocal (fun x => hregular x.property)
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.mp hG.isPreconnected
  obtain ⟨x0, hx0⟩ := hG.nonempty
  let x : G := ⟨x0, hx0⟩
  have hsame : ∀ y : G, B y = B x := fun y => hconst.apply_eq_of_preconnectedSpace y x
  refine ⟨B x, ⟨(hB x).1, ?_, ?_⟩, ?_⟩
  · intro y hy
    simpa only [hsame ⟨y,hy⟩] using hlocal ⟨y,hy⟩
  · apply closure_minimal _ (ht.tile_isClosed hT (hB x).1)
    intro y hy
    have hmem := (hB ⟨y,hy⟩).2
    simpa only [hsame ⟨y,hy⟩] using hmem
  · intro C hC
    exact ht.eq_of_common_local_germ hC.1 (hB x).1
      (hC.2.1 x0 hx0) (hlocal x) (hregular hx0)

/-- The preceding endpoint retains the fact that the physical companion differs
from the root tile. The condition is checked pointwise, not inferred from a
face-to-face convention. -/
theorem exists_companion_closed_face (ht : IsTiling T tiles)
    (hT : IsCompact T) {A F G H : Set (Point d)} (hG : IsConnected G)
    (hFG : F ⊆ closure G) (hregular : G ⊆ closure (interior H))
    (hex : ∀ x ∈ G, ∃ B ∈ incidentTiles tiles x, B ≠ A ∧ LocalSetEq x B H) :
    ∃ B ∈ tiles, B ≠ A ∧ F ⊆ B ∧
      (∀ x ∈ G, LocalSetEq x B H) ∧
      ∀ x ∈ G, ∀ C ∈ tiles, LocalSetEq x C H → C = B := by
  obtain ⟨B, hB, _⟩ := ht.exists_unique_companion_on_connected_set hT hG hregular
    (fun x hx => by obtain ⟨C,hC,_,hl⟩ := hex x hx; exact ⟨C,hC,hl⟩)
  have huniq : ∀ x ∈ G, ∀ C ∈ tiles, LocalSetEq x C H → C = B := by
    intro x hx C hC hl
    exact ht.eq_of_common_local_germ hC hB.1 hl (hB.2.1 x hx) (hregular hx)
  refine ⟨B,hB.1,?_,hFG.trans hB.2.2,hB.2.1,huniq⟩
  obtain ⟨x,hx⟩ := hG.nonempty
  obtain ⟨C,hC,hCA,hl⟩ := hex x hx
  exact (huniq x hx C hC.1 hl) ▸ hCA

/-- Intrinsic face-chart version. This accepts a connected set of points in any
subspace chart and the equality of closures produced by generic-face selection.
Only continuity of the chart is used, so no ambient openness is required. -/
theorem exists_companion_closed_face_intrinsic (ht : IsTiling T tiles)
    (hT : IsCompact T) {X : Type*} [TopologicalSpace X]
    (p : X → Point d) (hp : Continuous p)
    {A H : Set (Point d)} {G O : Set X} (hG : IsConnected G)
    (hdense : closure G = closure O)
    (hregular : ∀ x ∈ G, p x ∈ closure (interior H))
    (hex : ∀ x ∈ G, ∃ B ∈ incidentTiles tiles (p x),
      B ≠ A ∧ LocalSetEq (p x) B H) :
    ∃ B ∈ tiles, B ≠ A ∧ p '' closure O ⊆ B ∧
      (∀ x ∈ G, LocalSetEq (p x) B H) ∧
      ∀ x ∈ G, ∀ C ∈ tiles, LocalSetEq (p x) C H → C = B := by
  have hconn : IsConnected (p '' G) := hG.image p hp.continuousOn
  have hr : p '' G ⊆ closure (interior H) := by
    rintro _ ⟨x,hx,rfl⟩; exact hregular x hx
  have he : ∀ y ∈ p '' G, ∃ B ∈ incidentTiles tiles y,
      B ≠ A ∧ LocalSetEq y B H := by
    rintro _ ⟨x,hx,rfl⟩; exact hex x hx
  obtain ⟨B,hB,hBA,hcover,hl,hu⟩ := ht.exists_companion_closed_face hT hconn
    (Subset.refl (closure (p '' G))) hr he
  refine ⟨B,hB,hBA,?_,fun x hx => hl (p x) ⟨x,hx,rfl⟩,
    fun x hx C hC => hu (p x) ⟨x,hx,rfl⟩ C hC⟩
  rw [← hdense]
  exact (image_closure_subset_closure_image hp).trans hcover

/-- A closed physical tile contains every limit of its generic face points,
including a crease point that need not lie in the relative interior of a facet. -/
theorem companion_mem_of_mem_closure (ht : IsTiling T tiles) (hT : IsCompact T)
    {B G : Set (Point d)} (hB : B ∈ tiles) (hGB : G ⊆ B)
    {y : Point d} (hy : y ∈ closure G) : y ∈ B :=
  closure_minimal hGB (ht.tile_isClosed hT hB) hy

/-- Intrinsic closure version for face-to-crease limits. -/
theorem companion_mem_of_intrinsic_closure (ht : IsTiling T tiles) (hT : IsCompact T)
    {X : Type*} [TopologicalSpace X] (p : X → Point d) (hp : Continuous p)
    {B : Set (Point d)} (hB : B ∈ tiles) {G : Set X}
    (hGB : ∀ x ∈ G, p x ∈ B) {y : X} (hy : y ∈ closure G) : p y ∈ B :=
  closure_minimal hGB ((ht.tile_isClosed hT hB).preimage hp) hy

/-- Once the crease sector count is two, every non-root incident physical tile
is the same tile. This is purely about physical sets, not chosen frames. -/
theorem companion_eq_of_incident_card_two
    {y : Point d} {A B C : Set (Point d)}
    (hcard : Nat.card (incidentTiles tiles y) = 2)
    (hA : A ∈ incidentTiles tiles y) (hB : B ∈ incidentTiles tiles y)
    (hC : C ∈ incidentTiles tiles y) (hBA : B ≠ A) (hCA : C ≠ A) : B = C := by
  rw [Nat.card_coe_set_eq] at hcard
  obtain ⟨D,E,_,hset⟩ := Set.ncard_eq_two.mp hcard
  rw [hset] at hA hB hC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB hC
  rcases hA with hA | hA
  · have hBD : B ≠ D := fun h => hBA (h.trans hA.symm)
    have hCD : C ≠ D := fun h => hCA (h.trans hA.symm)
    exact (hB.resolve_left hBD).trans (hC.resolve_left hCD).symm
  · have hBE : B ≠ E := fun h => hBA (h.trans hA.symm)
    have hCE : C ≠ E := fun h => hCA (h.trans hA.symm)
    exact (hB.resolve_right hBE).trans (hC.resolve_right hCE).symm

/-- K2 propagation: approach a crease point through either generic face.
Closedness puts both face companions at the crease, and the independently
proved two-tile sector count identifies them. No facet-interior premise occurs. -/
theorem face_companions_eq_at_crease (ht : IsTiling T tiles) (hT : IsCompact T)
    {A B C G F : Set (Point d)} {y : Point d}
    (hA : A ∈ incidentTiles tiles y) (hB : B ∈ tiles) (hC : C ∈ tiles)
    (hBA : B ≠ A) (hCA : C ≠ A)
    (hGB : G ⊆ B) (hFC : F ⊆ C)
    (hyG : y ∈ closure G) (hyF : y ∈ closure F)
    (hcard : Nat.card (incidentTiles tiles y) = 2) : B = C := by
  exact companion_eq_of_incident_card_two hcard hA
    ⟨hB, ht.companion_mem_of_mem_closure hT hB hGB hyG⟩
    ⟨hC, ht.companion_mem_of_mem_closure hT hC hFC hyF⟩ hBA hCA

/-- K2 with already-closed face coverage, useful after K1 continuation. -/
theorem closed_face_companions_eq_at_crease
    {A B C F₁ F₂ : Set (Point d)} {y : Point d}
    (hA : A ∈ incidentTiles tiles y) (hB : B ∈ tiles) (hC : C ∈ tiles)
    (hBA : B ≠ A) (hCA : C ≠ A)
    (hF₁B : F₁ ⊆ B) (hF₂C : F₂ ⊆ C) (hy₁ : y ∈ F₁) (hy₂ : y ∈ F₂)
    (hcard : Nat.card (incidentTiles tiles y) = 2) : B = C :=
  companion_eq_of_incident_card_two hcard hA ⟨hB,hF₁B hy₁⟩ ⟨hC,hF₂C hy₂⟩ hBA hCA

end IsTiling

#print axioms LocalSetEq.not_disjoint_interiors
#print axioms IsTiling.companionAssignment_isLocallyConstant
#print axioms IsTiling.exists_unique_companion_on_connected_set
#print axioms IsTiling.exists_companion_closed_face
#print axioms IsTiling.exists_companion_closed_face_intrinsic
#print axioms IsTiling.companion_mem_of_intrinsic_closure
#print axioms IsTiling.face_companions_eq_at_crease
#print axioms IsTiling.closed_face_companions_eq_at_crease

end SparseMonotiles
