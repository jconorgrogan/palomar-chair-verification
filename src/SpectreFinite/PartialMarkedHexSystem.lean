module

public import SpectreFinite.HexRotationComposition
public import SpectreFinite.AreaBoundaryGrowth

@[expose] public section


/-! Finite marked hex systems with partial ports. No geometric embedding,
free lattice action, substitution operation, or infinite field is assumed.
The graph-ball estimates count explicit lists, allowing repeated vertices. -/
namespace SpectreFinite.HexSearch

structure PartialMarkedHexSystem where
  cellCount : Nat
  label : Fin cellCount → State
  step : Fin 6 → Fin cellCount → Option (Fin cellCount)

namespace PartialMarkedHexSystem

abbrev Cell (S : PartialMarkedHexSystem) := Fin S.cellCount

def mark (S : PartialMarkedHexSystem) (v : S.Cell) (d : Fin 6) : Int :=
  facingMark (placed ((0,0), S.label v)) d

/-- The triangle law closes an elementary triangle whenever the two adjacent
ports from its root exist. In particular it imposes no artificial closure at
a boundary corner where either of those ports is absent. -/
structure WellFormed (S : PartialMarkedHexSystem) : Prop where
  opposite_inverse : ∀ d v w, S.step d v = some w → S.step (opposite d) w = some v
  matching : ∀ d v w, S.step d v = some w → S.mark v d = -S.mark w (opposite d)
  triangle : ∀ d v w z, S.step d v = some w →
    S.step (rotateTurn 1 d) v = some z → S.step (rotateTurn 2 d) w = some z

def cells (S : PartialMarkedHexSystem) : List S.Cell := List.finRange S.cellCount

def ports (S : PartialMarkedHexSystem) : List (S.Cell × Fin 6) :=
  S.cells.flatMap fun v => (List.finRange 6).map fun d => (v,d)

/-- The boundary is computed from the partial neighbor maps, not supplied as
an unrelated numerical certificate. -/
def boundaryPorts (S : PartialMarkedHexSystem) : List (S.Cell × Fin 6) :=
  S.ports.filter fun p => decide (S.step p.2 p.1 = none)

def boundaryVertices (S : PartialMarkedHexSystem) : List S.Cell :=
  S.cells.filter fun v => (List.finRange 6).any fun d => (S.step d v).isNone

@[simp] theorem mem_cells (S : PartialMarkedHexSystem) (v : S.Cell) : v ∈ S.cells := by
  simp [cells]

@[simp] theorem cells_length (S : PartialMarkedHexSystem) : S.cells.length = S.cellCount := by
  simp [cells]

@[simp] theorem mem_ports (S : PartialMarkedHexSystem) (v : S.Cell) (d : Fin 6) :
    (v,d) ∈ S.ports := by simp [ports]

@[simp] theorem mem_boundaryPorts (S : PartialMarkedHexSystem) (v : S.Cell) (d : Fin 6) :
    (v,d) ∈ S.boundaryPorts ↔ S.step d v = none := by
  simp [boundaryPorts]

@[simp] theorem mem_boundaryVertices (S : PartialMarkedHexSystem) (v : S.Cell) :
    v ∈ S.boundaryVertices ↔ ∃ d, S.step d v = none := by
  simp [boundaryVertices, Option.isNone_iff_eq_none]

/-- A closed one-step neighborhood, with at most seven entries. Repetitions
are retained, so all subsequent bounds are valid without injectivity. -/
def neighbors (S : PartialMarkedHexSystem) (v : S.Cell) : List S.Cell :=
  v :: (List.finRange 6).filterMap fun d => S.step d v

@[simp] theorem mem_neighbors (S : PartialMarkedHexSystem) (v w : S.Cell) :
    w ∈ S.neighbors v ↔ w = v ∨ ∃ d, S.step d v = some w := by
  simp [neighbors, List.mem_filterMap]

theorem neighbors_length_le (S : PartialMarkedHexSystem) (v : S.Cell) :
    (S.neighbors v).length ≤ 7 := by
  have h := List.length_filterMap_le (f := fun d => S.step d v) (l := List.finRange 6)
  simpa [neighbors] using Nat.succ_le_succ h

theorem neighbors_symmetric (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    {v w : S.Cell} (h : w ∈ S.neighbors v) : v ∈ S.neighbors w := by
  rcases (S.mem_neighbors v w).mp h with rfl | ⟨d,hd⟩
  · simp
  · exact (S.mem_neighbors w v).mpr (Or.inr ⟨opposite d,hs.opposite_inverse d v w hd⟩)

/-- The list of endpoints of all padded paths of exactly R steps. Since a
stay-put move is included, its membership is distance at most R. -/
def ball (S : PartialMarkedHexSystem) : Nat → S.Cell → List S.Cell
  | 0, v => [v]
  | R+1, v => (S.neighbors v).flatMap (S.ball R)

@[simp] theorem mem_ball_zero (S : PartialMarkedHexSystem) (v w : S.Cell) :
    w ∈ S.ball 0 v ↔ w = v := by simp [ball]

theorem mem_ball_succ (S : PartialMarkedHexSystem) (R : Nat) (v w : S.Cell) :
    w ∈ S.ball (R+1) v ↔ ∃ u ∈ S.neighbors v, w ∈ S.ball R u := by
  simp [ball]

theorem self_mem_ball (S : PartialMarkedHexSystem) (R : Nat) (v : S.Cell) :
    v ∈ S.ball R v := by
  induction R with
  | zero => simp
  | succ R ih => exact (S.mem_ball_succ R v v).mpr ⟨v,by simp,ih⟩

theorem ball_append_step (S : PartialMarkedHexSystem) (R : Nat) {v w z : S.Cell}
    (hw : w ∈ S.ball R v) (hz : z ∈ S.neighbors w) : z ∈ S.ball (R+1) v := by
  induction R generalizing v with
  | zero =>
      have hv : w = v := (S.mem_ball_zero v w).mp hw
      subst w
      exact (S.mem_ball_succ 0 v z).mpr ⟨z,hz,by simp⟩
  | succ R ih =>
      obtain ⟨u,hu,hw⟩ := (S.mem_ball_succ R v w).mp hw
      exact (S.mem_ball_succ (R+1) v z).mpr ⟨u,hu,ih hw⟩

theorem ball_symmetric (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (R : Nat) {v w : S.Cell} (h : w ∈ S.ball R v) : v ∈ S.ball R w := by
  induction R generalizing v w with
  | zero => simpa using ((S.mem_ball_zero v w).mp h).symm
  | succ R ih =>
      obtain ⟨u,hu,hw⟩ := (S.mem_ball_succ R v w).mp h
      exact S.ball_append_step R (ih hw) (S.neighbors_symmetric hs hu)

private theorem length_flatMap_le {α β : Type} (A : List α) (f : α → List β) (K : Nat)
    (h : ∀ a ∈ A, (f a).length ≤ K) : (A.flatMap f).length ≤ A.length*K := by
  induction A with
  | nil => simp
  | cons a A ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,
        Nat.one_mul, Nat.add_comm] using Nat.add_le_add ha ht

theorem ball_length_le (S : PartialMarkedHexSystem) (R : Nat) (v : S.Cell) :
    (S.ball R v).length ≤ 7^R := by
  induction R generalizing v with
  | zero => simp [ball]
  | succ R ih =>
      calc
        (S.ball (R+1) v).length ≤ (S.neighbors v).length * 7^R :=
          length_flatMap_le (S.neighbors v) (S.ball R) (7^R) (fun w _ => ih w)
        _ ≤ 7*7^R := Nat.mul_le_mul_right _ (S.neighbors_length_le v)
        _ = 7^(R+1) := by rw [Nat.pow_succ,Nat.mul_comm]

/-- Every cell reachable within R steps has all six ports. The next cell at
distance R+1 need not itself have all ports. -/
def Deep (S : PartialMarkedHexSystem) (R : Nat) (root : S.Cell) : Prop :=
  ∀ v ∈ S.ball R root, ∀ d, ∃ w, S.step d v = some w

def boundaryCover (S : PartialMarkedHexSystem) (R : Nat) : List S.Cell :=
  S.boundaryPorts.flatMap fun p => S.ball R p.1

theorem boundaryCover_length_le (S : PartialMarkedHexSystem) (R : Nat) :
    (S.boundaryCover R).length ≤ S.boundaryPorts.length * 7^R :=
  length_flatMap_le S.boundaryPorts (fun p => S.ball R p.1) (7^R)
    (fun p _ => S.ball_length_le R p.1)

theorem cells_subset_boundaryCover_of_no_deep (S : PartialMarkedHexSystem)
    (hs : S.WellFormed) (R : Nat) (hno : ∀ root, ¬S.Deep R root) :
    S.cells ⊆ S.boundaryCover R := by
  classical
  intro root _
  obtain ⟨v,hv⟩ := Classical.not_forall.mp (hno root)
  have hvball : v ∈ S.ball R root := by
    by_cases h : v ∈ S.ball R root
    · exact h
    · exact False.elim (hv (fun hh => False.elim (h hh)))
  obtain ⟨d,hd⟩ := Classical.not_forall.mp (fun hh => hv (fun _ => hh))
  have hnone : S.step d v = none := by
    cases he : S.step d v with
    | none => rfl
    | some w => exact False.elim (hd ⟨w,he⟩)
  apply List.mem_flatMap.mpr
  exact ⟨(v,d),(S.mem_boundaryPorts v d).mpr hnone,S.ball_symmetric hs R hvball⟩

/-- A finite area-versus-actual-boundary estimate gives a genuinely deep
root. The proof needs inverse edges only; the remaining laws are recorded
for the later refinement and pullback construction. -/
theorem exists_deep_of_area_boundary (S : PartialMarkedHexSystem)
    (hs : S.WellFormed) (R : Nat)
    (hlarge : S.boundaryPorts.length * 7^R < S.cellCount) :
    ∃ root, S.Deep R root := by
  classical
  by_cases h : ∃ root, S.Deep R root
  · exact h
  · have hno : ∀ root, ¬S.Deep R root := fun root hr => h ⟨root,hr⟩
    have hcard := (List.nodup_finRange S.cellCount).length_le_of_subset
      (S.cells_subset_boundaryCover_of_no_deep hs R hno)
    have hcover := S.boundaryCover_length_le R
    change S.cells.length ≤ (S.boundaryCover R).length at hcard
    rw [S.cells_length] at hcard
    omega

/-- An explicit initial one-cell system. This does not define refinement. -/
def singleton (s : State) : PartialMarkedHexSystem where
  cellCount := 1
  label := fun _ => s
  step := fun _ _ => none

theorem singleton_wellFormed (s : State) : (singleton s).WellFormed := by
  constructor <;> intros <;> contradiction

@[simp] theorem singleton_boundary_length (s : State) :
    (singleton s).boundaryPorts.length = 6 := by
  rfl

end PartialMarkedHexSystem
end SpectreFinite.HexSearch
