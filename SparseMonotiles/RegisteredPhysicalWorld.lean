module

public import SparseMonotiles.ContactPhysicalOverlapTiles
public import SparseMonotiles.CarrierFacetHalfspace
public import SparseMonotiles.CarrierHierarchyCharts

@[expose] public section

/-!
# Registered physical tilings give complete carrier-cell worlds

Half-integer cell centres miss every certified key, so actual body membership at
those centres is exactly the binary-chair cell predicate. Consequently a
physical tiling whose frames have already been globally registered covers every
integer cell. Common occupied cells force actual interior overlap, giving unique
ownership. Global registration itself remains an explicit upstream premise.
-/
namespace SparseMonotiles
open Set Contact CarrierHierarchy
open scoped Topology

/-- A half-integer centre belongs to exactly one closed integer unit cell. -/
theorem cellCentre_mem_closedIntegerCell_iff {d : ℕ} (c b : Cell d) :
    cellCentre c ∈ closedIntegerCell b ↔ c=b := by
  constructor
  · intro h
    funext i
    have hi := h i
    change (b i : ℝ) ≤ (c i : ℝ)+1/2 ∧
      (c i : ℝ)+1/2 ≤ (b i : ℝ)+1 at hi
    have hbc : (b i : ℝ) < ((c i+1 : ℤ) : ℝ) := by push_cast; linarith
    have hcb : (c i : ℝ) < ((b i+1 : ℤ) : ℝ) := by push_cast; linarith
    have hb : b i < c i+1 := Int.cast_lt.mp hbc
    have hc : c i < b i+1 := Int.cast_lt.mp hcb
    omega
  · rintro rfl i
    change (c i : ℝ) ≤ (c i : ℝ)+1/2 ∧ (c i : ℝ)+1/2 ≤ (c i : ℝ)+1
    constructor <;> linarith

theorem cellCentre_mem_carrier_iff {d : ℕ} (c : Cell d) :
    cellCentre c ∈ carrier d ↔ IsChairCell c := by
  rw [mem_carrier_iff_exists_chairCell]
  simp only [cellCentre_mem_closedIntegerCell_iff]
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact hb
  · intro hc
    exact ⟨c,hc,rfl⟩

/-- Actual body membership, including its closure convention, is exact at all
cell centres; this is stronger than the one-way interior inclusion. -/
theorem cellCentre_mem_body_iff {d : ℕ} (ks : List (KeyData d))
    (mu : ℚ) (hmu : mu < 1/2)
    (hks : ∀ k ∈ ks, HasNormalIntegerBand mu k) (c : Cell d) :
    cellCentre c ∈ body ks ↔ IsChairCell c := by
  have hg : LocalSetEq (cellCentre c) (body ks) (carrier d) :=
    localSetEq_body_carrier_away_keys
      (Filter.Eventually.mono (show ∀ᶠ x in 𝓝 (cellCentre c), x ∈ integerCellCore mu c from
        (isOpen_integerCellCore mu c).mem_nhds (cellCentre_mem_integerCellCore mu hmu c))
        (fun x hx k hk hkey => Set.disjoint_left.mp
          (keySolid_disjoint_integerCellCore mu k (hks k hk) c) hkey hx))
  exact hg.mem_iff.trans (cellCentre_mem_carrier_iff c)

theorem posed_cellCentre_mem_iff {d : ℕ} {T : Set (Point d)}
    (hc : ∀ c : Cell d, cellCentre c ∈ T ↔ IsChairCell c)
    (p : Pose d) (c : Cell d) :
    cellCentre c ∈ p.euclidean '' T ↔ Occupies p c := by
  have he : p.euclidean (cellCentre (p.inverseCell c)) = cellCentre c := by
    rw [Pose.euclidean_cellCentre,Pose.cell_inverseCell]
  rw [← he]
  constructor
  · rintro ⟨x,hx,hxe⟩
    have hxv : x = cellCentre (p.inverseCell c) := p.euclidean.injective hxe
    subst x
    exact (hc _).mp hx
  · intro h
    exact ⟨cellCentre (p.inverseCell c),(hc _).mpr h,rfl⟩

theorem posed_cellCentre_mem_interior {d : ℕ} {T : Set (Point d)}
    (hc : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (p : Pose d) (c : Cell d) (h : Occupies p c) :
    cellCentre c ∈ interior (p.euclidean '' T) := by
  rw [show (p.euclidean : Point d → Point d) = p.euclidean.toHomeomorph from rfl]
  rw [← p.euclidean.toHomeomorph.image_interior]
  refine ⟨cellCentre (p.inverseCell c),hc _ h,?_⟩
  exact (p.euclidean_cellCentre _).trans (congrArg cellCentre (p.cell_inverseCell c))

/-- Construct the full registered carrier world from a registered physical
frame family. Neither integer-cell coverage nor unique ownership is assumed. -/
noncomputable def registeredWorldOfPhysicalFrames {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))} (ht : IsTiling T tiles)
    (hc : ∀ c : Cell d, cellCentre c ∈ T ↔ IsChairCell c)
    (hi : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (e : Point d ≃ᵢ Point d) (q : tiles → Pose d)
    (himage : ∀ A : tiles, e '' (A : Set (Point d)) = (q A).euclidean '' T) :
    RegisteredWorld d where
  tiles := Set.range q
  covers := by
    intro c
    obtain ⟨A,hA,hx⟩ := ht.2.1 (e.symm (cellCentre c))
    have hm : cellCentre c ∈ e '' A := ⟨e.symm (cellCentre c),hx,e.apply_symm_apply _⟩
    rw [himage ⟨A,hA⟩] at hm
    exact ⟨q ⟨A,hA⟩,⟨⟨A,hA⟩,rfl⟩,(posed_cellCentre_mem_iff hc _ c).mp hm⟩
  disjoint := by
    rintro p ⟨A,rfl⟩ s ⟨B,rfl⟩ c hp hs
    have hp' := posed_cellCentre_mem_interior hi (q A) c hp
    have hs' := posed_cellCentre_mem_interior hi (q B) c hs
    rw [← himage A] at hp'
    rw [← himage B] at hs'
    have hxA : e.symm (cellCentre c) ∈ interior (A : Set (Point d)) := by
      rw [show (e : Point d → Point d) = e.toHomeomorph from rfl,
        ← e.toHomeomorph.image_interior] at hp'
      rcases hp' with ⟨x,hx,he⟩
      simpa [← he] using hx
    have hxB : e.symm (cellCentre c) ∈ interior (B : Set (Point d)) := by
      rw [show (e : Point d → Point d) = e.toHomeomorph from rfl,
        ← e.toHomeomorph.image_interior] at hs'
      rcases hs' with ⟨x,hx,he⟩
      simpa [← he] using hx
    have hAB : A=B := by
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (ht.2.2 A A.property B B.property hne) hxA hxB
    exact congrArg q hAB

@[simp] theorem registeredWorldOfPhysicalFrames_tiles {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))} (ht : IsTiling T tiles)
    (hc : ∀ c : Cell d, cellCentre c ∈ T ↔ IsChairCell c)
    (hi : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (e : Point d ≃ᵢ Point d) (q : tiles → Pose d)
    (himage : ∀ A : tiles, e '' (A : Set (Point d)) = (q A).euclidean '' T) :
    (registeredWorldOfPhysicalFrames ht hc hi e q himage).tiles = Set.range q := rfl

theorem T5_cellCentre_mem_iff (c : Cell 5) : cellCentre c ∈ T5 ↔ IsChairCell c :=
  cellCentre_mem_body_iff keys5 (1/100) (by norm_num) keys5_normalBand c

theorem T7_cellCentre_mem_iff (c : Cell 7) : cellCentre c ∈ T7 ↔ IsChairCell c :=
  cellCentre_mem_body_iff keys7 (1/100) (by norm_num) keys7_normalBand c

noncomputable def T5_registeredWorld {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (e : Point 5 ≃ᵢ Point 5) (q : tiles → Pose 5)
    (himage : ∀ A : tiles, e '' (A : Set (Point 5)) = (q A).euclidean '' T5) :
    RegisteredWorld 5 :=
  registeredWorldOfPhysicalFrames ht T5_cellCentre_mem_iff
    (fun _ h => T5_cellCentre_mem_interior h) e q himage

noncomputable def T7_registeredWorld {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (e : Point 7 ≃ᵢ Point 7) (q : tiles → Pose 7)
    (himage : ∀ A : tiles, e '' (A : Set (Point 7)) = (q A).euclidean '' T7) :
    RegisteredWorld 7 :=
  registeredWorldOfPhysicalFrames ht T7_cellCentre_mem_iff
    (fun _ h => T7_cellCentre_mem_interior h) e q himage

#print axioms cellCentre_mem_body_iff
#print axioms registeredWorldOfPhysicalFrames
#print axioms T5_registeredWorld
#print axioms T7_registeredWorld
end SparseMonotiles
