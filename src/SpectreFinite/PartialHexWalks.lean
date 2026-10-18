module

public import SpectreFinite.PartialMarkedHexSystem

@[expose] public section


/-! Safe finite path evaluation in a partial marked hex system. Contextual
inverse and triangle reductions are proved from actual partial ports, not
postulated for an unconstructed total system. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem

/-- Directions are followed from the head of the list to its tail. -/
def walk (S : PartialMarkedHexSystem) : List (Fin 6) → S.Cell → Option S.Cell
  | [], v => some v
  | d :: tail, v => (S.step d v).bind (S.walk tail)

@[simp] theorem walk_nil (S : PartialMarkedHexSystem) (v : S.Cell) :
    S.walk [] v = some v := rfl

@[simp] theorem walk_singleton (S : PartialMarkedHexSystem) (d : Fin 6) (v : S.Cell) :
    S.walk [d] v = S.step d v := by
  simp [walk]

theorem walk_append (S : PartialMarkedHexSystem) (u v : List (Fin 6)) (root : S.Cell) :
    S.walk (u ++ v) root = (S.walk u root).bind (S.walk v) := by
  induction u generalizing root with
  | nil => rfl
  | cons d u ih =>
      simp only [List.cons_append,walk]
      cases h : S.step d root with
      | none => rfl
      | some w => exact ih w

theorem walk_mem_ball (S : PartialMarkedHexSystem) (word : List (Fin 6))
    {root endpoint : S.Cell} (h : S.walk word root = some endpoint) :
    endpoint ∈ S.ball word.length root := by
  induction word generalizing root with
  | nil => simpa [walk] using h.symm
  | cons d word ih =>
      cases he : S.step d root with
      | none => simp [walk,he] at h
      | some w =>
          have ht : S.walk word w = some endpoint := by simpa [walk,he] using h
          exact (S.mem_ball_succ word.length root endpoint).mpr
            ⟨w,(S.mem_neighbors root w).mpr (Or.inr ⟨d,he⟩),ih ht⟩

theorem ball_mono_one (S : PartialMarkedHexSystem) (R : Nat) (root : S.Cell) :
    S.ball R root ⊆ S.ball (R+1) root := by
  intro v hv
  exact (S.mem_ball_succ R root v).mpr ⟨root,by simp,hv⟩

theorem ball_mono (S : PartialMarkedHexSystem) {R T : Nat} (h : R ≤ T) (root : S.Cell) :
    S.ball R root ⊆ S.ball T root := by
  induction h with
  | refl => exact fun _ hv => hv
  | @step T h ih => exact fun v hv => S.ball_mono_one T root (ih hv)

theorem ball_add (S : PartialMarkedHexSystem) (R T : Nat) {root mid last : S.Cell}
    (hm : mid ∈ S.ball R root) (hl : last ∈ S.ball T mid) :
    last ∈ S.ball (R+T) root := by
  induction R generalizing root with
  | zero =>
      have he : mid = root := (S.mem_ball_zero root mid).mp hm
      subst mid
      simpa using hl
  | succ R ih =>
      obtain ⟨u,hu,hm⟩ := (S.mem_ball_succ R root mid).mp hm
      have hh := (S.mem_ball_succ (R+T) root last).mpr ⟨u,hu,ih hm⟩
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem Deep.mono (S : PartialMarkedHexSystem) {R T : Nat} {root : S.Cell}
    (h : S.Deep T root) (hle : R ≤ T) : S.Deep R root := by
  intro v hv d
  exact h v (S.ball_mono hle root hv) d

theorem Deep.at (S : PartialMarkedHexSystem) (R T : Nat) {root mid : S.Cell}
    (h : S.Deep (R+T) root) (hm : mid ∈ S.ball R root) : S.Deep T mid := by
  intro v hv d
  exact h v (S.ball_add R T hm hv) d

theorem Deep.step (S : PartialMarkedHexSystem) (R : Nat) {root next : S.Cell}
    (h : S.Deep (R+1) root) (d : Fin 6) (he : S.step d root = some next) :
    S.Deep R next := by
  apply Deep.at S 1 R (by simpa [Nat.add_comm] using h)
  exact (S.mem_ball_succ 0 root next).mpr
    ⟨next,(S.mem_neighbors root next).mpr (Or.inr ⟨d,he⟩),by simp⟩

/-- A depth-R root evaluates every word of length at most R. This formulation
keeps one spare complete layer, simplifying contextual rewrites. -/
theorem walk_exists (S : PartialMarkedHexSystem) (R : Nat) {root : S.Cell}
    (h : S.Deep R root) (word : List (Fin 6)) (hlen : word.length ≤ R) :
    ∃ endpoint, S.walk word root = some endpoint := by
  induction R generalizing root word with
  | zero =>
      have he : word = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst word
      exact ⟨root,rfl⟩
  | succ R ih =>
      cases word with
      | nil => exact ⟨root,rfl⟩
      | cons d word =>
          obtain ⟨next,he⟩ := h root (S.self_mem_ball (R+1) root) d
          obtain ⟨endpoint,hend⟩ := ih (Deep.step S R h d he) word (by simpa using hlen)
          exact ⟨endpoint,by simp [walk,he,hend]⟩

theorem deep_after_walk (S : PartialMarkedHexSystem) (R : Nat) (word : List (Fin 6))
    {root endpoint : S.Cell} (h : S.Deep (word.length+R) root)
    (he : S.walk word root = some endpoint) : S.Deep R endpoint :=
  Deep.at S word.length R h (S.walk_mem_ball word he)

/-- Cancellation only needs the first port to exist. -/
theorem walk_inverse (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) {root next : S.Cell} (he : S.step d root = some next) :
    S.walk [d,opposite d] root = some root := by
  simp [walk,he,hs.opposite_inverse d root next he]

/-- The finite-system triangle axiom yields the exact word rewrite. -/
theorem walk_triangle (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) {root left right : S.Cell}
    (hl : S.step d root = some left) (hr : S.step (rotateTurn 1 d) root = some right) :
    S.walk [d,rotateTurn 2 d] root = S.walk [rotateTurn 1 d] root := by
  simp [walk,hl,hr,hs.triangle d root left right hl hr]

/-- Contextual inverse cancellation is valid once the prefix reaches a
complete cell. The suffix may be arbitrary, including an escaping path. -/
theorem walk_cancel_context (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (u v : List (Fin 6)) (d : Fin 6) {root : S.Cell} (h : S.Deep u.length root) :
    S.walk (u ++ [d,opposite d] ++ v) root = S.walk (u ++ v) root := by
  obtain ⟨mid,hm⟩ := S.walk_exists u.length h u (by omega)
  obtain ⟨next,he⟩ := h mid (S.walk_mem_ball u hm) d
  simp only [List.append_assoc,S.walk_append,hm,Option.bind_some]
  rw [S.walk_inverse hs d he]
  rfl

/-- The analogous contextual triangle relation. -/
theorem walk_triangle_context (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (u v : List (Fin 6)) (d : Fin 6) {root : S.Cell} (h : S.Deep u.length root) :
    S.walk (u ++ [d,rotateTurn 2 d] ++ v) root =
      S.walk (u ++ [rotateTurn 1 d] ++ v) root := by
  obtain ⟨mid,hm⟩ := S.walk_exists u.length h u (by omega)
  obtain ⟨left,hl⟩ := h mid (S.walk_mem_ball u hm) d
  obtain ⟨right,hr⟩ := h mid (S.walk_mem_ball u hm) (rotateTurn 1 d)
  simp only [List.append_assoc,S.walk_append,hm,Option.bind_some]
  rw [S.walk_triangle hs d hl hr]

/-- Complementary facing marks along every successfully evaluated final
edge, independent of the lengths used to construct that path. -/
theorem matching_after_walk (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (u : List (Fin 6)) (d : Fin 6) {root a b : S.Cell}
    (ha : S.walk u root = some a) (hb : S.walk (u ++ [d]) root = some b) :
    S.mark a d = -S.mark b (opposite d) := by
  have he : S.step d a = some b := by simpa [S.walk_append,ha] using hb
  exact hs.matching d a b he

/-- A total label on words, using an arbitrary fallback only when the partial
walk is undefined. Bounded theorems below prove that the fallback is unused. -/
def wordLabel (S : PartialMarkedHexSystem) (root : S.Cell) (fallback : State)
    (word : List (Fin 6)) : State :=
  ((S.walk word root).map S.label).getD fallback

theorem wordLabel_of_walk (S : PartialMarkedHexSystem) (fallback : State)
    (word : List (Fin 6)) {root endpoint : S.Cell}
    (h : S.walk word root = some endpoint) :
    S.wordLabel root fallback word = S.label endpoint := by
  simp [wordLabel,h]

theorem wordLabel_cancel_context (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (fallback : State) (u v : List (Fin 6)) (d : Fin 6) {root : S.Cell}
    (h : S.Deep u.length root) :
    S.wordLabel root fallback (u ++ [d,opposite d] ++ v) =
      S.wordLabel root fallback (u ++ v) := by
  unfold wordLabel
  rw [S.walk_cancel_context hs u v d h]

theorem wordLabel_triangle_context (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (fallback : State) (u v : List (Fin 6)) (d : Fin 6) {root : S.Cell}
    (h : S.Deep u.length root) :
    S.wordLabel root fallback (u ++ [d,rotateTurn 2 d] ++ v) =
      S.wordLabel root fallback (u ++ [rotateTurn 1 d] ++ v) := by
  unfold wordLabel
  rw [S.walk_triangle_context hs u v d h]

theorem wordLabel_matching (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (fallback : State) (u : List (Fin 6)) (d : Fin 6) {root : S.Cell}
    (h : S.Deep (u.length+1) root) :
    facingMark (placed ((0,0), S.wordLabel root fallback u)) d =
      -facingMark (placed ((0,0), S.wordLabel root fallback (u ++ [d]))) (opposite d) := by
  obtain ⟨a,ha⟩ := S.walk_exists (u.length+1) h u (by omega)
  obtain ⟨b,hb⟩ := S.walk_exists (u.length+1) h (u ++ [d]) (by simp)
  rw [S.wordLabel_of_walk fallback u ha,S.wordLabel_of_walk fallback (u ++ [d]) hb]
  exact S.matching_after_walk hs u d ha hb

end SpectreFinite.HexSearch.PartialMarkedHexSystem
