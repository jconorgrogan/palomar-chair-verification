module

public import SpectreGeometry.ReverseAnchorHomeomorphism
public import SpectreClusters.ReverseClusterCocycle
public import SpectreClusters.ReverseClusterDeltaBounds
public import SpectreFinite.LiteralMarkedFieldExistence

@[expose] public section


/-! Actual globally legal54-state marked fields have a genuine whole-plane
anchor homeomorphism. The cluster-carrier and physical P existence bridges
are separate and are not asserted by this module. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open SpectreFinite SpectreFinite.HexSearch
open SpectreClusters SpectreClusters.ReverseExistence

def anchorRealPoint (p : Point) : AnchorPlane := (p.1,p.2)

def markedAnchor (f : Position → State) (hf : GloballyLegal f) (x : Position) : AnchorPlane :=
  anchorRealPoint (lattice (developedAnchor f hf x))

theorem markedAnchor_step (f : Position → State) (hf : GloballyLegal f)
    (x : Position) (d : Fin 6) :
    markedAnchor f hf (addPos x (SpectreFinite.direction d)) = markedAnchor f hf x+
      anchorRealPoint (vertexDelta (f x) (f (addPos x (SpectreFinite.direction d))) d) := by
  unfold markedAnchor
  rw [developedAnchor_step,lattice_add,centerDelta_lattice _ _ _ (field_sideMatch f hf x d)]
  ext <;> simp [anchorRealPoint,SpectreClusters.add]

theorem markedAnchor_residualBounds (f : Position → State) (hf : GloballyLegal f) :
    AnchorResidualBounds (markedAnchor f hf) := by
  have he (n m : ℤ) := vertexDelta_mem_options (f (n,m))
    (f (addPos (n,m) (SpectreFinite.direction 3))) 3 (field_sideMatch f hf (n,m) 3)
  have hn (n m : ℤ) := vertexDelta_mem_options (f (n,m))
    (f (addPos (n,m) (SpectreFinite.direction 4))) 4 (field_sideMatch f hf (n,m) 4)
  have hE (n m : ℤ) := east_options_bounds _ (he n m)
  have hN (n m : ℤ) := north_options_bounds _ (hn n m)
  have epos (n m : ℤ) : addPos (n,m) (SpectreFinite.direction 3) = (n+1,m) := by
    change (n+1,m+0) = (n+1,m)
    simp
  have npos (n m : ℤ) : addPos (n,m) (SpectreFinite.direction 4) = (n,m+1) := by
    change (n+0,m+1) = (n,m+1)
    simp
  have e (n m : ℤ) := markedAnchor_step f hf (n,m) 3
  have n (a b : ℤ) := markedAnchor_step f hf (a,b) 4
  simp only [epos] at e hE
  simp only [npos] at n hN
  constructor
  · intro a b
    rw [e a b]
    simp only [Prod.fst_add,anchorRealPoint]
    have h1 : (8:ℝ) ≤ (vertexDelta (f (a,b)) (f (a+1,b)) 3).1 := by exact_mod_cast (hE a b).1
    have h2 : ((vertexDelta (f (a,b)) (f (a+1,b)) 3).1:ℝ) ≤ 18 := by exact_mod_cast (hE a b).2.1
    apply abs_le.mpr
    constructor <;> linarith
  · intro a b
    rw [n a b]
    simp only [Prod.fst_add,anchorRealPoint]
    have h1 : (-2:ℝ) ≤ (vertexDelta (f (a,b)) (f (a,b+1)) 4).1 := by exact_mod_cast (hN a b).1
    have h2 : ((vertexDelta (f (a,b)) (f (a,b+1)) 4).1:ℝ) ≤ 6 := by exact_mod_cast (hN a b).2.1
    apply abs_le.mpr
    constructor <;> linarith
  · intro a b
    rw [e a b]
    simp only [Prod.snd_add,anchorRealPoint]
    have h1 : (-6:ℝ) ≤ (vertexDelta (f (a,b)) (f (a+1,b)) 3).2 := by exact_mod_cast (hE a b).2.2.1
    have h2 : ((vertexDelta (f (a,b)) (f (a+1,b)) 3).2:ℝ) ≤ 2 := by exact_mod_cast (hE a b).2.2.2
    apply abs_le.mpr
    constructor <;> linarith
  · intro a b
    rw [n a b]
    simp only [Prod.snd_add,anchorRealPoint]
    have h1 : (6:ℝ) ≤ (vertexDelta (f (a,b)) (f (a,b+1)) 4).2 := by exact_mod_cast (hN a b).2.2.1
    have h2 : ((vertexDelta (f (a,b)) (f (a,b+1)) 4).2:ℝ) ≤ 14 := by exact_mod_cast (hN a b).2.2.2
    apply abs_le.mpr
    constructor <;> linarith

/-- Constructed from the actual marked field; injectivity and surjectivity
follow from the finite neighbor envelope and the Banach inverse. -/
def markedAnchorHomeomorph (f : Position → State) (hf : GloballyLegal f) :
    AnchorPlane ≃ₜ AnchorPlane := anchorHomeomorph (markedAnchor f hf) (markedAnchor_residualBounds f hf)

@[simp] theorem markedAnchorHomeomorph_integer (f : Position → State) (hf : GloballyLegal f)
    (n m : ℤ) : markedAnchorHomeomorph f hf (n,m) = markedAnchor f hf (n,m) :=
  anchorHomeomorph_integer _ _ n m

theorem developedAnchor_injective (f : Position → State) (hf : GloballyLegal f) :
    Function.Injective (SpectreClusters.ReverseExistence.developedAnchor f hf) := by
  intro x y hxy
  have hm : markedAnchor f hf x = markedAnchor f hf y := by
    unfold markedAnchor
    rw [hxy]
  have he : markedAnchorHomeomorph f hf ((x.1:ℝ),(x.2:ℝ)) =
      markedAnchorHomeomorph f hf ((y.1:ℝ),(y.2:ℝ)) := by
    simpa only [markedAnchorHomeomorph_integer] using hm
  have hi := (markedAnchorHomeomorph f hf).injective he
  apply Prod.ext
  · have h : (x.1 : ℝ) = (y.1 : ℝ) := congrArg Prod.fst hi
    exact_mod_cast h
  · have h : (x.2 : ℝ) = (y.2 : ℝ) := congrArg Prod.snd hi
    exact_mod_cast h

theorem exists_marked_field_with_anchor_homeomorph :
    ∃ (f : Position → State) (hf : GloballyLegal f) (H : AnchorPlane ≃ₜ AnchorPlane),
      ∀ n m : ℤ, H (n,m) = markedAnchor f hf (n,m) := by
  obtain ⟨f,hf⟩ := PartialMarkedHexSystem.exists_globallyLegal_from_literal_substitution
  exact ⟨f,hf,markedAnchorHomeomorph f hf,markedAnchorHomeomorph_integer f hf⟩

end
end SpectreGeometry.ReverseExistence
