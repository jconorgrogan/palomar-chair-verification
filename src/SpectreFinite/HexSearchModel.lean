module

public import SpectreFinite.ListedPatches
public import SpectreFinite.PatchEnumeration

@[expose] public section


/-! Explicit finite-domain marked-hexagon search specification. No large
search is evaluated here, and no local-parent completeness is asserted. -/
namespace SpectreFinite.HexSearch
abbrev Position := Int × Int
abbrev State := TileKind × Fin 6

def stateChoices : List State :=
  (List.finRange 9).flatMap (fun k => (List.finRange 6).map (fun r => (k,r)))

theorem mem_stateChoices (s : State) : s ∈ stateChoices := by
  rcases s with ⟨k,r⟩
  simp [stateChoices]

theorem stateChoices_size : stateChoices.length = 54 := by decide

def placed (x : Position × State) : PlacedHex :=
  ⟨x.2.1,x.2.2,x.1.1,x.1.2⟩

def Matches (x y : Position × State) : Prop := CompatiblePair (placed x) (placed y)
instance : DecidableRel Matches := fun _ _ => inferInstanceAs (Decidable (CompatiblePair _ _))

/-- An explicit radius-n axial ball. This definition is not a proof that a
paper's corona convention agrees with this domain. -/
def hexRegion (n : Nat) : List Position :=
  ((List.range (2*n+1)).flatMap (fun q : Nat =>
    (List.range (2*n+1)).map (fun r : Nat => ((q : Int)-(n : Int),(r : Int)-(n : Int))))).filter
      (fun p => decide ((p.1+p.2).natAbs ≤ n))

/-- Exact finite domain size; no state assignment search is executed. -/
theorem hexRegion_five_size : (hexRegion 5).length = 91 := by decide

theorem hexRegion_five_nodup : (hexRegion 5).Nodup := by decide

def assignments (positions : List Position) : List (List (Position × State)) :=
  Search.enumerate (fun _ => stateChoices) Matches positions

/-- Complete finite search semantics for this exact alphabet and matching
rule. This does not state that the search has been evaluated or classify
its survivors into the nine proposed parents. -/
theorem mem_assignments_iff (positions : List Position) (p : List (Position × State)) :
    p ∈ assignments positions ↔ p.map Prod.fst = positions ∧ p.Pairwise Matches := by
  rw [assignments, Search.mem_enumerate_iff]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · exact fun h => ⟨h.1,h.2,fun x _ => mem_stateChoices x.2⟩


/-- The exact six-direction compatibility relation is symmetric; finite
search list order therefore does not orient the matching rule. -/
theorem compatiblePair_symm (a b : PlacedHex) (h : CompatiblePair a b) :
    CompatiblePair b a := by
  refine ⟨Ne.symm h.1, ?_⟩
  intro d hd
  have hq := congrArg Prod.fst hd
  have hr := congrArg Prod.snd hd
  simp only [addPos] at hq hr
  have hb : pos b = addPos (pos a) (direction (opposite d)) := by
    rw [direction_opposite]
    apply Prod.ext
    · change (pos b).1 = (pos a).1 + -(direction d).1
      omega
    · change (pos b).2 = (pos a).2 + -(direction d).2
      omega
  have hc := h.2 (opposite d) hb
  rw [opposite_involutive] at hc
  omega

theorem matches_symm (x y : Position × State) (h : Matches x y) : Matches y x :=
  compatiblePair_symm (placed x) (placed y) h

#print axioms mem_stateChoices
#print axioms stateChoices_size
#print axioms hexRegion_five_size
#print axioms hexRegion_five_nodup
#print axioms mem_assignments_iff
#print axioms compatiblePair_symm
#print axioms matches_symm
end SpectreFinite.HexSearch
