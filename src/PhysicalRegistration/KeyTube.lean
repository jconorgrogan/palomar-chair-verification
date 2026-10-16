module

public import PhysicalRegistration.TubeAssembly

@[expose] public section


/-!
Centered concrete key tubes, compatibility at footprint boundaries, and
local transfer to the literal tube-replacement body.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def centeredGraphHypograph (center n : E) (H : E → ℝ) : Set E :=
  {x | ⟪n, x - center⟫_ℝ ≤ H (x - center)}

noncomputable def centeredGraphHypograph_local_graph
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ x y, |H x - H y| ≤ L * ‖x - y‖)
    (hshift : ∀ (x : E) (s : ℝ), H (x + s • n) = H x)
    (x : E) (hx : ⟪n, x - center⟫_ℝ = H (x - center)) :
    LocalLipschitzGraphAt (centeredGraphHypograph center n H) x L := by
  let H' : E → ℝ := fun y => H (y - center) + ⟪n, center⟫_ℝ
  have hH' : ∀ y z, |H' y - H' z| ≤ L * ‖y - z‖ := by
    intro y z
    have h := hH (y - center) (z - center)
    have hid : y - center - (z - center) = y - z := by abel
    simpa [H', hid] using h
  have hshift' : ∀ (y : E) (s : ℝ), H' (y + s • n) = H' y := by
    intro y s
    have hid : y + s • n - center = (y - center) + s • n := by abel
    simp only [H', hid, hshift]
  have hx' : ⟪n, x⟫_ℝ = H' x := by
    rw [inner_sub_right] at hx
    dsimp [H']
    linarith
  have heq : graphHypograph n H' = centeredGraphHypograph center n H := by
    ext y
    change (⟪n, y⟫_ℝ ≤ H (y - center) + ⟪n, center⟫_ℝ) ↔
      ⟪n, y - center⟫_ℝ ≤ H (y - center)
    rw [inner_sub_right]
    constructor <;> intro h <;> linarith
  rw [← heq]
  exact graphHypograph_local_graph n hn H' L hL hH' hshift' x hx'

theorem unit_inner_continuous (e : E) (he : ‖e‖ = 1) :
    Continuous (fun x : E => ⟪e, x⟫_ℝ) := by
  have h : LipschitzWith 1 (fun x : E => ⟪e, x⟫_ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := affine_unit_axis_lipschitz e he 1 0 1 (by norm_num) x y
    simpa [Real.dist_eq, dist_eq_norm] using h
  exact h.continuous

theorem centeredGraphHypograph_isClosed (center n : E) (hn : ‖n‖ = 1)
    (H : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ x y, |H x - H y| ≤ L * ‖x - y‖) :
    IsClosed (centeredGraphHypograph center n H) := by
  have hHlip : LipschitzWith ⟨L, hL⟩ H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (H x) (H y) ≤ L * dist x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hH x y
  exact isClosed_le
    ((unit_inner_continuous n hn).comp (continuous_id.sub continuous_const))
    (hHlip.continuous.comp (continuous_id.sub continuous_const))

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def centeredKeyTube (center n : E) (axis : ι → E) (eta rho : ℝ)
    (pMinus pPlus : ι → ℝ) : Set E :=
  {x | |⟪n, x - center⟫_ℝ| ≤ rho ∧ ∀ i,
    -eta / pMinus i ≤ ⟪axis i, x - center⟫_ℝ ∧
      ⟪axis i, x - center⟫_ℝ ≤ eta / pPlus i}

def strictCenteredKeyTube (center n : E) (axis : ι → E) (eta rho : ℝ)
    (pMinus pPlus : ι → ℝ) : Set E :=
  {x | |⟪n, x - center⟫_ℝ| < rho ∧ ∀ i,
    -eta / pMinus i < ⟪axis i, x - center⟫_ℝ ∧
      ⟪axis i, x - center⟫_ℝ < eta / pPlus i}

theorem centeredKeyTube_isClosed (center n : E) (hn : ‖n‖ = 1)
    (axis : ι → E) (haxis : ∀ i, ‖axis i‖ = 1) (eta rho : ℝ)
    (pMinus pPlus : ι → ℝ) :
    IsClosed (centeredKeyTube center n axis eta rho pMinus pPlus) := by
  have hncont : Continuous (fun x : E => ⟪n, x - center⟫_ℝ) :=
    (unit_inner_continuous n hn).comp (continuous_id.sub continuous_const)
  have hacont : ∀ i, Continuous (fun x : E => ⟪axis i, x - center⟫_ℝ) :=
    fun i => (unit_inner_continuous (axis i) (haxis i)).comp
      (continuous_id.sub continuous_const)
  simp only [centeredKeyTube, ofPred_and, ofPred_forall]
  apply IsClosed.inter (isClosed_le hncont.abs continuous_const)
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (hacont i)).inter
    (isClosed_le (hacont i) continuous_const)

theorem strictCenteredKeyTube_isOpen (center n : E) (hn : ‖n‖ = 1)
    (axis : ι → E) (haxis : ∀ i, ‖axis i‖ = 1) (eta rho : ℝ)
    (pMinus pPlus : ι → ℝ) :
    IsOpen (strictCenteredKeyTube center n axis eta rho pMinus pPlus) := by
  have hncont : Continuous (fun x : E => ⟪n, x - center⟫_ℝ) :=
    (unit_inner_continuous n hn).comp (continuous_id.sub continuous_const)
  have hacont : ∀ i, Continuous (fun x : E => ⟪axis i, x - center⟫_ℝ) :=
    fun i => (unit_inner_continuous (axis i) (haxis i)).comp
      (continuous_id.sub continuous_const)
  simp only [strictCenteredKeyTube, ofPred_and, ofPred_forall]
  apply IsOpen.inter (isOpen_lt hncont.abs continuous_const)
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (hacont i)).inter
    (isOpen_lt (hacont i) continuous_const)

theorem strictCenteredKeyTube_subset_interior (center n : E) (hn : ‖n‖ = 1)
    (axis : ι → E) (haxis : ∀ i, ‖axis i‖ = 1) (eta rho : ℝ)
    (pMinus pPlus : ι → ℝ) :
    strictCenteredKeyTube center n axis eta rho pMinus pPlus ⊆
      interior (centeredKeyTube center n axis eta rho pMinus pPlus) := by
  apply interior_maximal
  · intro x hx
    exact ⟨hx.1.le, fun i => ⟨(hx.2 i).1.le, (hx.2 i).2.le⟩⟩
  · exact strictCenteredKeyTube_isOpen center n hn axis haxis eta rho pMinus pPlus

/-- Within the normal strip, failure to lie in the tube interior forces the
actual zero-extended key height to vanish. This includes footprint edges. -/
theorem keyHeight_zero_outside_tube_interior (center n : E) (hn : ‖n‖ = 1)
    (axis : ι → E) (haxis : ∀ i, ‖axis i‖ = 1)
    (eta rho a N : ℝ) (heta : 0 < eta) (pMinus pPlus : ι → ℝ)
    (hMinus : ∀ i, 0 < pMinus i) (hPlus : ∀ i, 0 < pPlus i)
    (x : E) (hstrip : |⟪n, x - center⟫_ℝ| < rho)
    (hx : x ∉ interior (centeredKeyTube center n axis eta rho pMinus pPlus)) :
    keyHeight eta a N pMinus pPlus axis (x - center) = 0 := by
  by_contra hne
  apply hx
  apply strictCenteredKeyTube_subset_interior center n hn axis haxis eta rho pMinus pPlus
  exact ⟨hstrip, keyHeight_active_footprint eta a N heta pMinus pPlus axis
    hMinus hPlus (x - center) hne⟩

/-- The carrier and keyed hypograph agree off the interior of the key tube
whenever the carrier is actually a flat half-space in the chosen neighborhood. -/
theorem keyed_tube_boundary_compatibility (carrier U : Set E)
    (center n : E) (hn : ‖n‖ = 1) (axis : ι → E) (haxis : ∀ i, ‖axis i‖ = 1)
    (eta rho a N : ℝ) (heta : 0 < eta) (pMinus pPlus : ι → ℝ)
    (hMinus : ∀ i, 0 < pMinus i) (hPlus : ∀ i, 0 < pPlus i)
    (hflat : ∀ x ∈ U, x ∈ carrier ↔ ⟪n, x - center⟫_ℝ ≤ 0)
    (hstrip : ∀ x ∈ U, |⟪n, x - center⟫_ℝ| < rho) :
    ∀ x ∈ U, x ∉ interior (centeredKeyTube center n axis eta rho pMinus pPlus) →
      (x ∈ carrier ↔ x ∈ centeredGraphHypograph center n
        (keyHeight eta a N pMinus pPlus axis)) := by
  intro x hxU hxTube
  have hzero := keyHeight_zero_outside_tube_interior center n hn axis haxis
    eta rho a N heta pMinus pPlus hMinus hPlus x (hstrip x hxU) hxTube
  change (x ∈ carrier ↔ ⟪n, x - center⟫_ℝ ≤
    keyHeight eta a N pMinus pPlus axis (x - center))
  rw [hzero]
  exact hflat x hxU

/-- The concrete tent formula supplies the chart and boundary compatibility;
literal tube replacement then transfers it to the assembled actual set. -/
noncomputable def keyed_replacement_local_graph {κ : Type*}
    (carrier : Set E) (tube hypograph : κ → Set E) (i : κ)
    (center n : E) (hn : ‖n‖ = 1) (axis : ι → E)
    (haxis : ∀ j, ‖axis j‖ = 1) (horth : ∀ j, ⟪axis j, n⟫_ℝ = 0)
    (eta rho a N J pMax : ℝ) (heta : 0 < eta) (hN : 0 < N)
    (ha : |a| ≤ J) (hMax : 0 ≤ pMax) (pMinus pPlus : ι → ℝ)
    (hMinus : ∀ j, 0 < pMinus j ∧ pMinus j ≤ pMax)
    (hPlus : ∀ j, 0 < pPlus j ∧ pPlus j ≤ pMax)
    (htube : tube i = centeredKeyTube center n axis eta rho pMinus pPlus)
    (hhypo : hypograph i = centeredGraphHypograph center n
      (keyHeight eta a N pMinus pPlus axis))
    (U : Set E) (hU : IsOpen U) (x : E) (hxU : x ∈ U)
    (hxgraph : ⟪n, x - center⟫_ℝ = keyHeight eta a N pMinus pPlus axis (x - center))
    (hother : ∀ j, j ≠ i → Disjoint U (tube j))
    (hflat : ∀ y ∈ U, y ∈ carrier ↔ ⟪n, y - center⟫_ℝ ≤ 0)
    (hstrip : ∀ y ∈ U, |⟪n, y - center⟫_ℝ| < rho) :
    LocalLipschitzGraphAt (replaceTubes carrier tube hypograph) x (J * pMax / N) := by
  have hL : 0 ≤ J * pMax / N :=
    div_nonneg (mul_nonneg ((abs_nonneg a).trans ha) hMax) hN.le
  let G := centeredGraphHypograph_local_graph center n hn
    (keyHeight eta a N pMinus pPlus axis) (J * pMax / N) hL
    (keyHeight_lipschitz eta a N J pMax heta hN ha hMax pMinus pPlus axis
      (fun j => ⟨(hMinus j).1.le, (hMinus j).2⟩)
      (fun j => ⟨(hPlus j).1.le, (hPlus j).2⟩) haxis)
    (keyHeight_normal_shift eta a N pMinus pPlus axis n horth) x hxgraph
  have G' : LocalLipschitzGraphAt (hypograph i) x (J * pMax / N) := by
    rw [hhypo]
    exact G
  apply replaceTubes_local_graph carrier tube hypograph i G' U hU hxU hother
  intro y hy hyTube
  rw [htube] at hyTube
  rw [hhypo]
  exact keyed_tube_boundary_compatibility carrier U center n hn axis haxis
    eta rho a N heta pMinus pPlus (fun j => (hMinus j).1) (fun j => (hPlus j).1)
    hflat hstrip y hy hyTube

#print axioms centeredGraphHypograph_local_graph
#print axioms centeredGraphHypograph_isClosed
#print axioms centeredKeyTube_isClosed
#print axioms strictCenteredKeyTube_subset_interior
#print axioms keyHeight_zero_outside_tube_interior
#print axioms keyed_tube_boundary_compatibility
#print axioms keyed_replacement_local_graph
end PhysicalRegistration
