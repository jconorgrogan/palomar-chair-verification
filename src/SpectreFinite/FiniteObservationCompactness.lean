module

public import SpectreFinite.HexSearchModel
public import SpectreFinite.FiniteAlphabetCompactness

@[expose] public section


/-! Compactness for finite observations of the fixed 54-state alphabet on
any explicitly exhausted countable domain. The finite constraint predicate
is arbitrary; actual bounded witnesses remain an explicit input. -/
namespace SpectreFinite.HexSearch.FiniteObservations
variable {D : Type u} [DecidableEq D]

abbrev Observation (D : Type u) := List (D × State)

def read : Observation D → D → State
  | [],_ => (0,0)
  | e::es,x => if e.1 = x then e.2 else read es x

def restrict (f : D → State) (domain : List D) : Observation D :=
  domain.map fun x => (x,f x)

theorem read_restrict (f : D → State) (domain : List D) (x : D) (hx : x ∈ domain) :
    read (restrict f domain) x = f x := by
  induction domain with
  | nil => simp at hx
  | cons a as ih =>
    by_cases ha : a = x
    · subst a; simp [restrict,read]
    · have ht : x ∈ as := by simpa [List.mem_cons,Ne.symm ha] using hx
      simpa [restrict,read,ha] using ih ht

theorem read_of_mem (p : Observation D) (hn : (p.map Prod.fst).Nodup)
    (x : D) (s : State) (hx : (x,s) ∈ p) : read p x = s := by
  induction p with
  | nil => simp at hx
  | cons e es ih =>
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hx with he | hx
    · subst e; simp [read]
    · have hxe : e.1 ≠ x := by
        intro he
        apply hh.1
        exact List.mem_map.mpr ⟨(x,s),hx,he.symm⟩
      simpa [read,hxe] using ih hh.2 hx

theorem restrict_read (p : Observation D) (hn : (p.map Prod.fst).Nodup) :
    restrict (read p) (p.map Prod.fst) = p := by
  unfold restrict
  rw [List.map_map]
  have he : ∀ e ∈ p, (e.1,read p e.1) = e := by
    intro e he
    exact Prod.ext rfl (read_of_mem p hn e.1 e.2 he)
  simpa [Function.comp_def] using List.map_congr_left he

def choices (domain : List D) : List (Observation D) :=
  Search.enumerate (fun _ => stateChoices) (fun _ _ => True) domain

omit [DecidableEq D] in
theorem restrict_mem_choices (f : D → State) (domain : List D) :
    restrict f domain ∈ choices domain := by
  apply (Search.mem_enumerate_iff _ _ domain _).mpr
  refine ⟨by simp [restrict,List.map_map,Function.comp_def],?_,?_⟩
  · exact List.pairwise_of_forall_mem_list (fun _ _ _ _ => True.intro)
  · intro x hx; exact mem_stateChoices x.2

omit [DecidableEq D] in
theorem choices_domain (domain : List D) (p : Observation D) (hp : p ∈ choices domain) :
    p.map Prod.fst = domain := ((Search.mem_enumerate_iff _ _ domain p).mp hp).1

def Coherent (windows : List (Observation D)) : Prop :=
  ∀ p ∈ windows, ∀ q ∈ windows, ∀ x,
    x ∈ p.map Prod.fst → x ∈ q.map Prod.fst → read p x = read q x

theorem restriction_coherent (f : D → State) (domains : Nat → List D) (n : Nat) :
    Coherent ((List.range n).map fun i => restrict f (domains i)) := by
  intro p hp q hq x hxp hxq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have hxi : x ∈ domains i := by simpa [restrict,List.map_map,Function.comp_def] using hxp
  have hxj : x ∈ domains j := by simpa [restrict,List.map_map,Function.comp_def] using hxq
  rw [read_restrict f _ x hxi,read_restrict f _ x hxj]

/-- Compactness with concrete finite branching; the conclusion preserves
all finite observations, rather than presupposing a coherent infinite limit. -/
theorem exists_function (domains : Nat → List D)
    (hn : ∀ n, (domains n).Nodup)
    (radius : D → Nat) (hcover : ∀ x, x ∈ domains (radius x))
    (Good : Observation D → Prop)
    (hfinite : ∀ n, ∃ f : D → State, ∀ i, i ≤ n → Good (restrict f (domains i))) :
    ∃ f : D → State, ∀ n, Good (restrict f (domains n)) := by
  let P : List (Observation D) → Prop := fun xs => Coherent xs ∧ ∀ p ∈ xs, Good p
  have hhered : ∀ xs n, P xs → P (xs.take n) := by
    intro xs n h
    refine ⟨?_,?_⟩
    · intro p hp q hq x hxp hxq
      exact h.1 p (List.mem_of_mem_take hp) q (List.mem_of_mem_take hq) x hxp hxq
    · intro p hp; exact h.2 p (List.mem_of_mem_take hp)
  have hlong : ∀ n, ∃ word : List (Observation D), P word ∧ n ≤ word.length ∧
      ∀ i (hi : i < word.length), word[i] ∈ choices (domains i) := by
    intro n
    obtain ⟨f,hf⟩ := hfinite n
    refine ⟨(List.range n).map (fun i => restrict f (domains i)),⟨restriction_coherent f domains n,?_⟩,
      by simp,?_⟩
    · intro p hp
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
      exact hf i (Nat.le_of_lt (List.mem_range.mp hi))
    · intro i hi
      simp only [List.getElem_map,List.getElem_range]
      exact restrict_mem_choices f _
  obtain ⟨stream,hp,hs⟩ := FiniteAlphabetCompactness.exists_stream_of_getElem
    (fun n => choices (domains n)) P hhered hlong
  have hd : ∀ n, (stream n).map Prod.fst = domains n := fun n => choices_domain _ _ (hs n)
  have hg : ∀ n, Good (stream n) := by
    intro n
    exact (hp (n+1)).2 _ (List.mem_map.mpr ⟨n,List.mem_range.mpr (by omega),rfl⟩)
  have agree : ∀ i j x, x ∈ domains i → x ∈ domains j → read (stream i) x = read (stream j) x := by
    intro i j x hi hj
    exact (hp (i+j+1)).1 _ (List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩)
      _ (List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩) x
      (by simpa only [hd i] using hi) (by simpa only [hd j] using hj)
  let f : D → State := fun x => read (stream (radius x)) x
  refine ⟨f,?_⟩
  intro n
  have he : restrict f (domains n) = stream n := by
    have hh := restrict_read (stream n) (by rw [hd n]; exact hn n)
    rw [hd n] at hh
    rw [← hh]
    apply List.map_congr_left
    intro x hx
    exact Prod.ext rfl (agree (radius x) n x (hcover x) hx)
  rw [he]
  exact hg n

end SpectreFinite.HexSearch.FiniteObservations
