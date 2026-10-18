module

public import Init

@[expose] public section


/-!
Exact combinatorial kite grid for the Spectre paper's hat/turtle analysis.
The vertex embedding is (sqrt(3)*x/2, x/2+y). No real-plane registration
or physical contact theorem is assumed or asserted by this module.
-/
namespace SpectreClusters

abbrev Point := Int × Int
abbrev Turn := Fin 6

def add (a b : Point) : Point := (a.1+b.1,a.2+b.2)
def sub (a b : Point) : Point := (a.1-b.1,a.2-b.2)
def rotate (k : Turn) (p : Point) : Point :=
  match k.val with
  | 0 => p
  | 1 => (-p.2,p.1+p.2)
  | 2 => (-p.1-p.2,p.1)
  | 3 => (-p.1,-p.2)
  | 4 => (p.2,-p.1-p.2)
  | _ => (p.1+p.2,-p.1)

def turnAdd (a b : Turn) : Turn := ⟨(a.val+b.val)%6, Nat.mod_lt _ (by decide)⟩
def lattice (p : Point) : Point := (4*p.1+2*p.2,-2*p.1+2*p.2)

theorem add_sub_cancel (a b : Point) : add (sub a b) b = a := by
  apply Prod.ext <;> simp [add,sub]

theorem sub_eq_of_add_eq (a b c : Point) (h : add a b = c) : a = sub c b := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp [add,sub] at * <;> omega

theorem add_assoc (a b c : Point) : add (add a b) c = add a (add b c) := by
  apply Prod.ext <;> simp [add,Int.add_assoc]

theorem rotate_add (k : Turn) (a b : Point) :
    rotate k (add a b) = add (rotate k a) (rotate k b) := by
  have hk := k.isLt
  have hs : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 := by omega
  rcases hs with h|h|h|h|h|h <;>
    apply Prod.ext <;> simp [rotate,add,h] <;> omega

theorem lattice_injective (a b : Point) (h : lattice a = lattice b) : a = b := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp [lattice] at * <;> omega

theorem lattice_add (a b : Point) : lattice (add a b) = add (lattice a) (lattice b) := by
  apply Prod.ext <;> simp [lattice,add] <;> omega

theorem lattice_rotate (k : Turn) (p : Point) :
    lattice (rotate k p) = rotate k (lattice p) := by
  have hk := k.isLt
  have hs : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 := by omega
  rcases hs with h|h|h|h|h|h <;>
    apply Prod.ext <;> simp [rotate,lattice,h] <;> omega

structure Cell where
  center : Point
  sector : Turn
  deriving DecidableEq, Repr

def kiteVertices : List Point := [(0,0),(2,-1),(2,0),(1,1)]
def localVertices (k : Turn) : List Point := kiteVertices.map (rotate k)
def cellVertices (c : Cell) : List Point :=
  (localVertices c.sector).map (add (lattice c.center))

def translateCell (p : Point) (c : Cell) : Cell := ⟨add p c.center,c.sector⟩
def rotateCell (k : Turn) (c : Cell) : Cell :=
  ⟨rotate k c.center,turnAdd k c.sector⟩
def moveCell (k : Turn) (p : Point) (c : Cell) : Cell :=
  translateCell p (rotateCell k c)

/-- Vertex-incidence contact. The physical closed-kite contact equivalence
must be proved separately before applying this to a real tiling. -/
def CellContact (a b : Cell) : Prop :=
  ∃ v ∈ cellVertices a, v ∈ cellVertices b
instance (a b : Cell) : Decidable (CellContact a b) :=
  inferInstanceAs (Decidable (∃ v ∈ cellVertices a, v ∈ cellVertices b))

/-- Uniform finite local coordinate bound, proved on all six exact sectors. -/
theorem localVertices_bounds : ∀ k : Turn, ∀ v ∈ localVertices k,
    -2 ≤ v.1 ∧ v.1 ≤ 2 ∧ -2 ≤ v.2 ∧ v.2 ≤ 2 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide)
      (Fin.cases (by decide) (fun i => Fin.elim0 i))))))

/-- All vertex-contacting cells have center offsets in a fixed 5-by-5 box.
No disk, simply-connected union, or extendability assumption is used. -/
theorem contact_center_bounds (a b : Cell) (h : CellContact a b) :
    -2 ≤ b.center.1-a.center.1 ∧ b.center.1-a.center.1 ≤ 2 ∧
    -2 ≤ b.center.2-a.center.2 ∧ b.center.2-a.center.2 ≤ 2 := by
  obtain ⟨v,ha,hb⟩ := h
  obtain ⟨va,hva,ea⟩ := List.mem_map.mp ha
  obtain ⟨vb,hvb,eb⟩ := List.mem_map.mp hb
  have hba := localVertices_bounds a.sector va hva
  have hbb := localVertices_bounds b.sector vb hvb
  have hx := congrArg Prod.fst (ea.trans eb.symm)
  have hy := congrArg Prod.snd (ea.trans eb.symm)
  simp [add,lattice] at hx hy
  omega

/-- Deliberately conservative finite neighborhood. False positives are allowed. -/
def contactCandidates (a : Cell) : List Cell :=
  [-2,-1,0,1,2].flatMap fun q =>
    [-2,-1,0,1,2].flatMap fun r =>
      (List.finRange 6).map fun k => ⟨add a.center (q,r),k⟩

/-- Exhaustive for every grid cell, not just a sampled literal family. -/
theorem cellContact_mem_candidates (a b : Cell) (h : CellContact a b) :
    b ∈ contactCandidates a := by
  obtain ⟨hq0,hq1,hr0,hr1⟩ := contact_center_bounds a b h
  have hq : b.center.1-a.center.1 ∈ ([-2,-1,0,1,2] : List Int) := by simp; omega
  have hr : b.center.2-a.center.2 ∈ ([-2,-1,0,1,2] : List Int) := by simp; omega
  apply List.mem_flatMap.mpr
  refine ⟨b.center.1-a.center.1,hq,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b.center.2-a.center.2,hr,?_⟩
  apply List.mem_map.mpr
  refine ⟨b.sector,List.mem_finRange _,?_⟩
  cases b
  congr 1
  apply Prod.ext <;> simp [add] <;> omega

end SpectreClusters
