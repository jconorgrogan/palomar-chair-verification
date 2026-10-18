module

public import SparseMonotiles.KeyCovariance
public import SparseMonotiles.CarrierFacetHalfspace

@[expose] public section

/-!
# Checked finite supports for literal pyramid keys

Integer bounding intervals contain the whole convex-hull solid. Checked collar
bounds separate keys on distinct exposed grid facets; checked tangential gaps
separate different keys on the same facet. The resulting closed-support atlas
supplies actual isolated-key germs of `Model.body`, including its final closure.
-/

namespace SparseMonotiles

open Set Filter
open scoped Topology

/-- A closed coordinate support containing a key's base and its apex. -/
def keyCoordinateSupport {d : ℕ} (k : KeyData d) : Set (Point d) :=
  {x | ∀ i,
    min ((k.centre i : ℝ) - (k.radius i : ℝ)) (k.apex i : ℝ) ≤ x i ∧
    x i ≤ max ((k.centre i : ℝ) + (k.radius i : ℝ)) (k.apex i : ℝ)}

/-- Coordinate bounds extend from the base and apex to their full convex hull. -/
theorem keySolid_subset_coordinateSupport {d : ℕ} (k : KeyData d) :
    keySolid k ⊆ keyCoordinateSupport k := by
  intro x hx i
  let lo := min ((k.centre i : ℝ) - (k.radius i : ℝ)) (k.apex i : ℝ)
  let hi := max ((k.centre i : ℝ) + (k.radius i : ℝ)) (k.apex i : ℝ)
  have hf : IsLinearMap ℝ (fun y : Point d => y i) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsub : insert (rationalPoint k.apex) (keyBase k) ⊆
      {y : Point d | lo ≤ y i ∧ y i ≤ hi} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · have hb := abs_le.mp (hy i)
      exact ⟨(min_le_left _ _).trans (by linarith [hb.1]),
        (show y i ≤ (k.centre i : ℝ) + (k.radius i : ℝ) by linarith [hb.2]).trans
          (le_max_left _ _)⟩
  exact convexHull_min hsub
    ((convex_halfSpace_ge hf lo).inter (convex_halfSpace_le hf hi)) hx

/-- Supports are closed, so avoiding finitely many supplies an open neighborhood. -/
theorem keyCoordinateSupport_isClosed {d : ℕ} (k : KeyData d) :
    IsClosed (keyCoordinateSupport k) := by
  have hcoord (i : Fin d) : Continuous (fun x : Point d => x i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have heq : keyCoordinateSupport k = ⋂ i : Fin d,
      {x : Point d |
        min ((k.centre i : ℝ) - (k.radius i : ℝ)) (k.apex i : ℝ) ≤ x i ∧
        x i ≤ max ((k.centre i : ℝ) + (k.radius i : ℝ)) (k.apex i : ℝ)} := by
    ext x
    simp only [keyCoordinateSupport, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (hcoord i)).inter
      (isClosed_le (hcoord i) continuous_const)

namespace Contact

/-- Integer endpoints include both base extremes and the apex. -/
def BoxKey.lowerBound {d : ℕ} (k : BoxKey d) (i : Fin d) : ℤ :=
  min (k.centre i - k.radius i) (k.apex i)

def BoxKey.upperBound {d : ℕ} (k : BoxKey d) (i : Fin d) : ℤ :=
  max (k.centre i + k.radius i) (k.apex i)

/-- Integer-only certificate for the closed normal `1/8`, tangential `1/4` collar. -/
def BoxKey.CollarValid {d : ℕ} (den : ℤ) (f : Facet d) (k : BoxKey d) : Prop :=
  (∀ i, i = f.axis →
    -den ≤ 8 * (k.lowerBound i - den * f.gridFacet.anchor i) ∧
    8 * (k.upperBound i - den * f.gridFacet.anchor i) ≤ den) ∧
  (∀ i, i ≠ f.axis →
    den * (4 * f.gridFacet.anchor i + 1) ≤ 4 * k.lowerBound i ∧
    4 * k.upperBound i ≤ den * (4 * f.gridFacet.anchor i + 3))

instance {d : ℕ} (den : ℤ) (f : Facet d) (k : BoxKey d) :
    Decidable (BoxKey.CollarValid den f k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A strict tangential interval gap separates even the closed pyramid supports. -/
def BoxKey.Separated {d : ℕ} (axis : Fin d) (k l : BoxKey d) : Prop :=
  ∃ i, i ≠ axis ∧
    (k.upperBound i < l.lowerBound i ∨ l.upperBound i < k.lowerBound i)

instance {d : ℕ} (axis : Fin d) (k l : BoxKey d) :
    Decidable (BoxKey.Separated axis k l) :=
  inferInstanceAs (Decidable (∃ i : Fin d, i ≠ axis ∧
    (k.upperBound i < l.lowerBound i ∨ l.upperBound i < k.lowerBound i)))

/-- Exact denominator-clearing for the real closed support. -/
theorem BoxKey.mem_coordinateSupport_iff {d : ℕ} {den : ℤ} (hd : 0 < den)
    (k : BoxKey d) (x : Point d) :
    x ∈ keyCoordinateSupport (k.toKeyData den) ↔
      ∀ i, (k.lowerBound i : ℝ) ≤ x i * (den : ℝ) ∧
        x i * (den : ℝ) ≤ (k.upperBound i : ℝ) := by
  have hd' : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  simp only [keyCoordinateSupport, Set.mem_setOf_eq, BoxKey.toKeyData,
    rationalVertex, Rat.cast_div, Rat.cast_intCast, ← sub_div, ← add_div,
    min_div_div_right hd'.le, max_div_div_right hd'.le,
    BoxKey.lowerBound, BoxKey.upperBound, Int.cast_min, Int.cast_max,
    Int.cast_sub, Int.cast_add, div_le_iff₀ hd', le_div_iff₀ hd']

/-- The finite integer inequalities contain the entire closed coordinate support. -/
theorem BoxKey.coordinateSupport_subset_collar {d : ℕ} {den : ℤ}
    (hd : 0 < den) {f : Facet d} {k : BoxKey d} (h : k.CollarValid den f) :
    keyCoordinateSupport (k.toKeyData den) ⊆ gridFacetCollar f.gridFacet := by
  intro x hx
  have hd' : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hb := (k.mem_coordinateSupport_iff hd x).mp hx
  constructor
  · have hn := h.1 f.axis rfl
    have hlo : -(den : ℝ) ≤ 8 * ((k.lowerBound f.axis : ℝ) -
        (den : ℝ) * (f.gridFacet.anchor f.axis : ℝ)) := by exact_mod_cast hn.1
    have hhi : 8 * ((k.upperBound f.axis : ℝ) -
        (den : ℝ) * (f.gridFacet.anchor f.axis : ℝ)) ≤ (den : ℝ) := by
      exact_mod_cast hn.2
    have hb' := hb f.axis
    change |x f.axis - (f.gridFacet.anchor f.axis : ℝ)| ≤ 1 / 8
    apply abs_le.mpr
    constructor <;> nlinarith [hb'.1, hb'.2]
  · intro i hi
    have ht := h.2 i hi
    have hlo : (den : ℝ) * (4 * (f.gridFacet.anchor i : ℝ) + 1) ≤
        4 * (k.lowerBound i : ℝ) := by exact_mod_cast ht.1
    have hhi : 4 * (k.upperBound i : ℝ) ≤
        (den : ℝ) * (4 * (f.gridFacet.anchor i : ℝ) + 3) := by exact_mod_cast ht.2
    have hb' := hb i
    apply abs_le.mpr
    constructor <;> nlinarith [hb'.1, hb'.2]

/-- Collar containment is a theorem about the whole convex-hull pyramid. -/
theorem BoxKey.keySolid_subset_collar {d : ℕ} {den : ℤ}
    (hd : 0 < den) {f : Facet d} {k : BoxKey d} (h : k.CollarValid den f) :
    keySolid (k.toKeyData den) ⊆ gridFacetCollar f.gridFacet :=
  (keySolid_subset_coordinateSupport _).trans (BoxKey.coordinateSupport_subset_collar hd h)

/-- A checked tangential gap gives disjoint closed real supports. -/
theorem BoxKey.Separated.coordinateSupports_disjoint {d : ℕ} {den : ℤ}
    (hd : 0 < den) {axis : Fin d} {k l : BoxKey d} (h : k.Separated axis l) :
    Disjoint (keyCoordinateSupport (k.toKeyData den))
      (keyCoordinateSupport (l.toKeyData den)) := by
  apply Set.disjoint_left.mpr
  intro x hk hl
  rcases h with ⟨i, _, hgap | hgap⟩
  · have hki := ((k.mem_coordinateSupport_iff hd x).mp hk) i
    have hli := ((l.mem_coordinateSupport_iff hd x).mp hl) i
    have hg : (k.upperBound i : ℝ) < (l.lowerBound i : ℝ) := by exact_mod_cast hgap
    linarith
  · have hki := ((k.mem_coordinateSupport_iff hd x).mp hk) i
    have hli := ((l.mem_coordinateSupport_iff hd x).mp hl) i
    have hg : (l.upperBound i : ℝ) < (k.lowerBound i : ℝ) := by exact_mod_cast hgap
    linarith

/-- In particular, the actual pyramid solids on a common facet are disjoint. -/
theorem BoxKey.Separated.keySolids_disjoint {d : ℕ} {den : ℤ}
    (hd : 0 < den) {axis : Fin d} {k l : BoxKey d} (h : k.Separated axis l) :
    Disjoint (keySolid (k.toKeyData den)) (keySolid (l.toKeyData den)) :=
  (h.coordinateSupports_disjoint hd).mono
    (keySolid_subset_coordinateSupport _) (keySolid_subset_coordinateSupport _)

/-- One finite row checks exposure, collar bounds, and all within-facet gaps. -/
def IndexedGeometry.AtlasValidAt {d n : ℕ} (g : IndexedGeometry d n) (i : Fin n) : Prop :=
  (¬ IsChairCell (g.facet i).neighbor) ∧
  (∀ k ∈ g.profile i, k.CollarValid g.denominator (g.facet i)) ∧
  (∀ k ∈ g.profile i, ∀ l ∈ g.profile i, k ≠ l →
    k.Separated (g.facet i).axis l)

instance {d n : ℕ} (g : IndexedGeometry d n) (i : Fin n) :
    Decidable (g.AtlasValidAt i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Every finite proof obligation is explicit; the atlas asserts no geometric fact. -/
def IndexedGeometry.SupportValid {d n : ℕ} (g : IndexedGeometry d n) : Prop :=
  0 < g.denominator ∧
  (∀ i, ∀ k ∈ g.profile i, k.CollarValid g.denominator (g.facet i)) ∧
  (∀ i, ∀ k ∈ g.profile i, ∀ l ∈ g.profile i, k ≠ l →
    k.Separated (g.facet i).axis l)

instance {d n : ℕ} (g : IndexedGeometry d n) : Decidable g.SupportValid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Row checks supply the support predicates; denominator positivity stays explicit. -/
theorem IndexedGeometry.supportValid_of_atlasValidAt {d n : ℕ}
    {g : IndexedGeometry d n} (hd : 0 < g.denominator)
    (h : ∀ i, g.AtlasValidAt i) : g.SupportValid :=
  ⟨hd, fun i => (h i).2.1, fun i => (h i).2.2⟩

/-- Cross-facet collar separation and within-facet interval separation combine. -/
theorem IndexedGeometry.coordinateSupports_disjoint {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {i j : Fin n} {k l : BoxKey d} (hk : k ∈ g.profile i) (hl : l ∈ g.profile j)
    (hne : k.toKeyData g.denominator ≠ l.toKeyData g.denominator) :
    Disjoint (keyCoordinateSupport (k.toKeyData g.denominator))
      (keyCoordinateSupport (l.toKeyData g.denominator)) := by
  by_cases hf : (g.facet i).gridFacet = (g.facet j).gridFacet
  · have hij : i = j := hunique
      (Facet.eq_of_gridFacet_eq (hexposed i) (howner j) hf)
    subst j
    apply BoxKey.Separated.coordinateSupports_disjoint h.1
    exact h.2.2 i k hk l hl (fun he => hne (congrArg (BoxKey.toKeyData g.denominator) he))
  · exact disjoint_of_subset_gridFacetCollars hf
      (BoxKey.coordinateSupport_subset_collar h.1 (h.2.1 i k hk))
      (BoxKey.coordinateSupport_subset_collar h.1 (h.2.1 j l hl))

/-- A one-way binding of every literal key is enough to transfer separation. -/
theorem IndexedGeometry.literal_coordinateSupports_disjoint {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    {k l : KeyData d} (hk : k ∈ ks) (hl : l ∈ ks) (hne : k ≠ l) :
    Disjoint (keyCoordinateSupport k) (keyCoordinateSupport l) := by
  rcases hbind k hk with ⟨i, b, hb, rfl⟩
  rcases hbind l hl with ⟨j, c, hc, rfl⟩
  exact IndexedGeometry.coordinateSupports_disjoint h hunique howner hexposed hb hc hne

/-- Every point of a selected key's support has an actual isolating neighborhood. -/
theorem IndexedGeometry.key_isolation {d n : ℕ} {g : IndexedGeometry d n}
    (h : g.SupportValid) (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    {k : KeyData d} (hk : k ∈ ks) {p : Point d} (hp : p ∈ keyCoordinateSupport k) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j := by
  apply key_isolation_of_disjoint_closed_supports keyCoordinateSupport
    (fun j _ => keySolid_subset_coordinateSupport j)
    (fun j _ _ => keyCoordinateSupport_isClosed j) ?_ hp
  intro j hj hne
  exact IndexedGeometry.literal_coordinateSupports_disjoint h hunique howner hexposed hbind hk hj hne.symm

/-- The literal body's local isolated-key model follows from the checked atlas. -/
theorem IndexedGeometry.localSetEq_body_isolated_key {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    {k : KeyData d} (hk : k ∈ ks) {p : Point d} (hp : p ∈ keyCoordinateSupport k) :
    LocalSetEq p (body ks)
      (closure (keyReplacement (carrier d) (keySolid k) k.bump)) :=
  SparseMonotiles.localSetEq_body_isolated_key hk
    (IndexedGeometry.key_isolation h hunique howner hexposed hbind hk hp)

/-- At each literal key point, the carrier is its proved exposed-facet halfspace. -/
theorem IndexedGeometry.localSetEq_body_isolated_halfspace {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    {k : KeyData d} (hk : k ∈ ks) {p : Point d} (hp : p ∈ keyCoordinateSupport k) :
    ∃ i, LocalSetEq p (body ks)
      (closure (keyReplacement (g.facet i).inwardHalfspace (keySolid k) k.bump)) := by
  rcases hbind k hk with ⟨i, b, hb, he⟩
  refine ⟨i, (g.facet i).localSetEq_body_isolated_halfspace
    (howner i) (hexposed i) hk ?_
    (IndexedGeometry.key_isolation h hunique howner hexposed hbind hk hp) (LocalSetEq.refl p _)⟩
  exact BoxKey.coordinateSupport_subset_collar h.1 (h.2.1 i b hb) (he.symm ▸ hp)

/-- The support atlas covers every point: either no key is locally present,
or exactly one key modifies its exposed carrier halfspace. -/
theorem IndexedGeometry.localSetEq_body_inventory {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    (p : Point d) :
    LocalSetEq p (body ks) (carrier d) ∨
      ∃ k ∈ ks, ∃ i, LocalSetEq p (body ks)
        (closure (keyReplacement (g.facet i).inwardHalfspace (keySolid k) k.bump)) := by
  by_cases hp : ∃ k ∈ ks, p ∈ keyCoordinateSupport k
  · rcases hp with ⟨k, hk, hp⟩
    rcases IndexedGeometry.localSetEq_body_isolated_halfspace
      h hunique howner hexposed hbind hk hp with ⟨i, hi⟩
    exact Or.inr ⟨k, hk, i, hi⟩
  · apply Or.inl
    apply SparseMonotiles.localSetEq_body_carrier_away_keys
    apply away_keys_of_closed_supports keyCoordinateSupport
      (fun j _ => keySolid_subset_coordinateSupport j)
      (fun j _ => keyCoordinateSupport_isClosed j)
    intro j hj hpj
    exact hp ⟨j, hj, hpj⟩

/-- The same complete support-level inventory holds for the physical boundary. -/
theorem IndexedGeometry.localSetEq_frontier_body_inventory {d n : ℕ}
    {g : IndexedGeometry d n} (h : g.SupportValid)
    (hunique : Function.Injective g.facet)
    (howner : ∀ i, IsChairCell (g.facet i).cell)
    (hexposed : ∀ i, ¬ IsChairCell (g.facet i).neighbor)
    {ks : List (KeyData d)}
    (hbind : ∀ k ∈ ks, ∃ i, ∃ b ∈ g.profile i, b.toKeyData g.denominator = k)
    (p : Point d) :
    LocalSetEq p (frontier (body ks)) (frontier (carrier d)) ∨
      ∃ k ∈ ks, ∃ i, LocalSetEq p (frontier (body ks))
        (frontier (closure
          (keyReplacement (g.facet i).inwardHalfspace (keySolid k) k.bump))) := by
  rcases IndexedGeometry.localSetEq_body_inventory h hunique howner hexposed hbind p with
    hcarrier | ⟨k, hk, i, hi⟩
  · exact Or.inl hcarrier.frontier
  · exact Or.inr ⟨k, hk, i, hi.frontier⟩

end Contact

#print axioms keySolid_subset_coordinateSupport
#print axioms Contact.BoxKey.keySolid_subset_collar
#print axioms Contact.BoxKey.Separated.keySolids_disjoint
#print axioms Contact.IndexedGeometry.coordinateSupports_disjoint
#print axioms Contact.IndexedGeometry.key_isolation
#print axioms Contact.IndexedGeometry.localSetEq_body_isolated_halfspace
#print axioms Contact.IndexedGeometry.localSetEq_frontier_body_inventory

end SparseMonotiles
