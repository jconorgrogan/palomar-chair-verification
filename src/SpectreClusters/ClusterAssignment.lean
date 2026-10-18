module

public import SpectreClusters.StageAT8ForcingData
public import SpectreClusters.StageAT7Alignment
public import SpectreClusters.ClusterOwnershipTransport
public import SpectreClusters.GridNeighborInvariant

@[expose] public section


/-! Canonical assignment rule: a turtle receives its eighth hat exactly
when that hat belongs to no T7H core. This module proves the structural
assignment and covariance laws; actual core ownership and uniqueness are
supplied by the checked field theorems in the final assembly. -/
namespace SpectreClusters.StageA

def extraAt (root : HTPlacement) : HTPlacement :=
  movePlacement root.turn root.center eighthHat

def ExtraCovered (f : Cell → HTPlacement) (root : HTPlacement) : Prop :=
  ∃ s, RootOwned f s ∧ s.kind = .turtle ∧ extraAt root ∈ clusterPiecesAt .t7h s

noncomputable def assignedKind (f : Cell → HTPlacement) (root : HTPlacement) : ClusterKind := by
  classical
  exact if ExtraCovered f root then .t7h else .t8h

noncomputable def assignedPieces (f : Cell → HTPlacement) (root : HTPlacement) : List HTPlacement :=
  clusterPiecesAt (assignedKind f root) root

theorem t7_piece_mem_t8 (root p : HTPlacement) (hp : p ∈ clusterPiecesAt .t7h root) :
    p ∈ clusterPiecesAt .t8h root := by
  obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨q,t7h_mem_t8h q hq,hqp⟩

theorem t8_piece_core_or_extra (root p : HTPlacement) (hp : p ∈ clusterPiecesAt .t8h root) :
    p ∈ clusterPiecesAt .t7h root ∨ p = extraAt root := by
  obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
  rcases t8h_member_core_or_extra q hq with hcore | rfl
  · exact Or.inl (List.mem_map.mpr ⟨q,hcore,hqp⟩)
  · exact Or.inr hqp.symm

theorem core_piece_assigned (f : Cell → HTPlacement) (root p : HTPlacement)
    (hp : p ∈ clusterPiecesAt .t7h root) : p ∈ assignedPieces f root := by
  classical
  by_cases h : ExtraCovered f root
  · simpa only [assignedPieces,assignedKind,if_pos h] using hp
  · simpa only [assignedPieces,assignedKind,if_neg h] using t7_piece_mem_t8 root p hp

theorem assigned_piece_core_or_free_extra (f : Cell → HTPlacement) (root p : HTPlacement)
    (hp : p ∈ assignedPieces f root) :
    p ∈ clusterPiecesAt .t7h root ∨ (¬ExtraCovered f root ∧ p = extraAt root) := by
  classical
  by_cases h : ExtraCovered f root
  · exact Or.inl (by simpa only [assignedPieces,assignedKind,if_pos h] using hp)
  · have ht : p ∈ clusterPiecesAt .t8h root := by
      simpa only [assignedPieces,assignedKind,if_neg h] using hp
    rcases t8_piece_core_or_extra root p ht with hc | he
    · exact Or.inl hc
    · exact Or.inr ⟨h,he⟩

theorem assigned_piece_mem_t8 (f : Cell → HTPlacement) (root p : HTPlacement)
    (hp : p ∈ assignedPieces f root) : p ∈ clusterPiecesAt .t8h root := by
  classical
  by_cases h : ExtraCovered f root
  · apply t7_piece_mem_t8 root p
    simpa only [assignedPieces,assignedKind,if_pos h] using hp
  · simpa only [assignedPieces,assignedKind,if_neg h] using hp

theorem extra_pose_injective (r s : HTPlacement) (hr : r.kind = .turtle)
    (hs : s.kind = .turtle) (he : extraAt r = extraAt s) : r = s := by
  have h := congrArg (fun p => alignTurtle p eighthHat) he
  change alignTurtle (movePlacement r.turn r.center eighthHat) eighthHat =
    alignTurtle (movePlacement s.turn s.center eighthHat) eighthHat at h
  rw [alignTurtle_moved r eighthHat hr,alignTurtle_moved s eighthHat hs] at h
  exact h

def UniqueCoreOwnership (f : Cell → HTPlacement) : Prop :=
  ∀ r s, RootOwned f r → r.kind = .turtle → RootOwned f s → s.kind = .turtle →
    ∀ p, p ∈ clusterPiecesAt .t7h r → p ∈ clusterPiecesAt .t7h s → r = s

theorem assigned_piece_unique_of_core_unique (f : Cell → HTPlacement)
    (hunique : UniqueCoreOwnership f) (r s : HTPlacement)
    (hr : RootOwned f r) (hkr : r.kind = .turtle)
    (hs : RootOwned f s) (hks : s.kind = .turtle) (p : HTPlacement)
    (hpr : p ∈ assignedPieces f r) (hps : p ∈ assignedPieces f s) : r = s := by
  rcases assigned_piece_core_or_free_extra f r p hpr with hrc | ⟨hrfree,hre⟩
  · rcases assigned_piece_core_or_free_extra f s p hps with hsc | ⟨hsfree,hse⟩
    · exact hunique r s hr hkr hs hks p hrc hsc
    · exact False.elim (hsfree ⟨r,hr,hkr,hse ▸ hrc⟩)
  · rcases assigned_piece_core_or_free_extra f s p hps with hsc | ⟨hsfree,hse⟩
    · exact False.elim (hrfree ⟨s,hs,hks,hre ▸ hsc⟩)
    · exact extra_pose_injective r s hkr hks (hre.symm.trans hse)

theorem extraAt_moved (k : Turn) (t : Point) (root : HTPlacement) :
    extraAt (movePlacement k t root) = movePlacement k t (extraAt root) := by
  exact (movePlacement_compose k root.turn t root.center eighthHat).symm

theorem extraCovered_moved (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root : HTPlacement) (h : ExtraCovered f root) :
    ExtraCovered (moveField k t f) (movePlacement k t root) := by
  obtain ⟨s,hs,hsk,he⟩ := h
  refine ⟨movePlacement k t s,moveField_rootOwned k t f s hs,hsk,?_⟩
  rw [extraAt_moved,clusterPiecesAt_moved]
  exact List.mem_map.mpr ⟨extraAt root,he,rfl⟩

theorem extraCovered_moved_iff (k : Turn) (t : Point)
    (f : Cell → HTPlacement) (root : HTPlacement) :
    ExtraCovered (moveField k t f) (movePlacement k t root) ↔ ExtraCovered f root := by
  constructor
  · intro h
    have hi := extraCovered_moved (turnNeg k) (inverseTranslation k t)
      (moveField k t f) (movePlacement k t root) h
    simpa only [moveField_inverse,movePlacement_inverse] using hi
  · exact extraCovered_moved k t f root

theorem assignedKind_moved (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root : HTPlacement) :
    assignedKind (moveField k t f) (movePlacement k t root) = assignedKind f root := by
  classical
  simp only [assignedKind,extraCovered_moved_iff]

theorem assignedPieces_moved (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root : HTPlacement) :
    assignedPieces (moveField k t f) (movePlacement k t root) =
      (assignedPieces f root).map (movePlacement k t) := by
  simp only [assignedPieces,assignedKind_moved,clusterPiecesAt_moved]

theorem moveField_eq_of_period (f : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod f u) : moveField 0 u f = f := by
  funext c
  have h := hperiod (moveCell (turnNeg 0) (inverseTranslation 0 u) c)
  rw [moveCell_right_inverse] at h
  exact h.symm

/-- The canonical T7H/T8H assignment preserves every translation of the
original tile-owner field, before any symbolic-coordinate identification. -/
theorem assignedPieces_translate_period (f : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod f u) (root : HTPlacement) :
    assignedPieces f (movePlacement 0 u root) =
      (assignedPieces f root).map (movePlacement 0 u) := by
  have h := assignedPieces_moved 0 u f root
  rw [moveField_eq_of_period f u hperiod] at h
  exact h

end SpectreClusters.StageA
