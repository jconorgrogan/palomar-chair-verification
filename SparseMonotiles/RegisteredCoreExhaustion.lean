module

public import SparseMonotiles.RegisteredIsometryGroup
public import SparseMonotiles.CorePoseCovariance
public import SparseMonotiles.GridCoreClamp

@[expose] public section

/-! A registered component which owns every open integer-cell core exhausts
an arbitrary physical tiling. The proof uses the actual quarter inball and
full core proximity, with no registration premise for the omitted tile. -/
namespace SparseMonotiles
open Set Contact

/-- Occupied cells supplied by the frames registered in one common ambient chart. -/
def registeredCoreCells {d : ℕ} {tiles : Set (Set (Point d))}
    (g : tiles → Point d ≃ᵢ Point d) (e : Point d ≃ᵢ Point d) : Set (Cell d) :=
  {c | ∃ A : tiles, ∃ q : Pose d,
    (g A).trans e = q.euclidean.toIsometryEquiv ∧ IsChairCell (q.inverseCell c)}

theorem registered_frames_of_all_core_cells {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (g : tiles → Point d ≃ᵢ Point d)
    (hg : ∀ A : tiles, g A '' T = (A : Set (Point d)))
    (e : Point d ≃ᵢ Point d) (mu : ℚ) (hmu : 0 < mu) (hmu' : mu < 1/4)
    (cores : ∀ bits : Fin d → Bool, (∃ i, bits i=false) →
      carrierCellCore mu bits ⊆ interior T)
    (p0 : Point d) (r : ℝ) (hball : Metric.ball p0 r ⊆ T)
    (hmargin : 2 * (d : ℝ) * (mu : ℝ) < r)
    (hcover : registeredCoreCells g e = univ) :
    ∀ B : tiles, IsRegisteredIsometry ((g B).trans e) := by
  classical
  intro B
  let G := (g B).trans e
  obtain ⟨c,y,hy,hclose⟩ := exists_mem_integerCellCore_dist_le mu hmu hmu' (G p0)
  have hc : c ∈ registeredCoreCells g e := by rw [hcover]; trivial
  obtain ⟨A,q,hq,hocc⟩ := hc
  have hAimage : e '' (A : Set (Point d)) = q.euclidean '' T := by
    calc
      e '' (A : Set (Point d)) = e '' (g A '' T) := congrArg (fun S => e '' S) (hg A).symm
      _ = ((g A).trans e) '' T := image_image e (g A) T
      _ = q.euclidean '' T := by rw [hq]; rfl
  have hyA := occupied_core_subset_posed_interior mu cores q c hocc hy
  rw [← hAimage] at hyA
  have hyball : y ∈ Metric.ball (G p0) r := by
    rw [Metric.mem_ball,dist_comm]
    exact hclose.trans_lt hmargin
  have hBimage : G '' T = e '' (B : Set (Point d)) := by
    calc
      G '' T = e '' (g B '' T) := (image_image e (g B) T).symm
      _ = e '' (B : Set (Point d)) := congrArg (fun S => e '' S) (hg B)
  have hBball : Metric.ball (G p0) r ⊆ interior (e '' (B : Set (Point d))) := by
    rw [← hBimage]
    apply interior_maximal ?_ Metric.isOpen_ball
    rw [← G.image_ball p0 r]
    exact image_mono hball
  have hyB := hBball hyball
  have hxA : e.symm y ∈ interior (A : Set (Point d)) := by
    rw [show (e : Point d → Point d) = e.toHomeomorph from rfl,
      ← e.toHomeomorph.image_interior] at hyA
    rcases hyA with ⟨x,hx,he⟩
    simpa [← he] using hx
  have hxB : e.symm y ∈ interior (B : Set (Point d)) := by
    rw [show (e : Point d → Point d) = e.toHomeomorph from rfl,
      ← e.toHomeomorph.image_interior] at hyB
    rcases hyB with ⟨x,hx,he⟩
    simpa [← he] using hx
  have hAB : A=B := by
    apply Subtype.ext
    by_cases he : (A : Set (Point d)) = (B : Set (Point d))
    · exact he
    · exact False.elim (Set.disjoint_left.mp (ht.2.2 A A.property B B.property he) hxA hxB)
  subst A
  exact ⟨q,hq⟩

theorem T5_registered_frames_of_all_core_cells
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5) (hg : ∀ A : tiles, g A '' T5 = (A : Set (Point 5)))
    (e : Point 5 ≃ᵢ Point 5) (hcover : registeredCoreCells g e = univ) :
    ∀ B : tiles, IsRegisteredIsometry ((g B).trans e) :=
  registered_frames_of_all_core_cells ht g hg e (1/100) (by norm_num) (by norm_num)
    T5_carrierCellCore_subset_interior (centralPoint 5) (1/4)
    T5_centralBall_from_cellCores (by norm_num) hcover

theorem T7_registered_frames_of_all_core_cells
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7) (hg : ∀ A : tiles, g A '' T7 = (A : Set (Point 7)))
    (e : Point 7 ≃ᵢ Point 7) (hcover : registeredCoreCells g e = univ) :
    ∀ B : tiles, IsRegisteredIsometry ((g B).trans e) :=
  registered_frames_of_all_core_cells ht g hg e (1/100) (by norm_num) (by norm_num)
    T7_carrierCellCore_subset_interior (centralPoint 7) (1/4)
    T7_centralBall_from_cellCores (by norm_num) hcover

#print axioms registered_frames_of_all_core_cells
#print axioms T5_registered_frames_of_all_core_cells
#print axioms T7_registered_frames_of_all_core_cells
end SparseMonotiles
