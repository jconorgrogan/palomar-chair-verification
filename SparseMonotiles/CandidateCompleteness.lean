module

public import SparseMonotiles.ContactIndexedChecker
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Option

@[expose] public section

/-!
# Completeness of the all-key-pair generator for registered full-key matches

The generator below implements the independent Python `pairpose` convention:
normal axes and opposed normal signs are forced by the two carrier facets;
tangent axes are looked up by their distinct half-widths; tangent signs are
recovered from nonzero apex offsets; translations are exact centre differences
and are retained only when integral. All ordered pairs are used, without a
component filter. The inverse-map check is a defensive check on malformed input.

The theorems start with an integer signed pose and an actual matching full box
signature. They do not assume candidate-list membership. Arbitrary-placement
registration, and recovering a full signature from an unlabelled physical
boundary patch, remain separate geometric questions.
-/
namespace SparseMonotiles.Contact

/-- The two asymmetries used by the independent pair generator. The normal zero
radius is included among the distinct widths; apex offsets are nonzero. -/
def BoxKey.Asymmetric {d : ℕ} (k : BoxKey d) : Prop :=
  Function.Injective k.radius ∧ ∀ i, k.apex i - k.centre i ≠ 0

instance {d : ℕ} (k : BoxKey d) : Decidable k.Asymmetric :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Finite, executable width lookup. Its fallback is irrelevant for valid pairs. -/
def widthAxis {d : ℕ} (k : BoxKey d) (fallback : Fin d) (width : ℤ) : Fin d :=
  ((List.finRange d).find? (fun j => decide (k.radius j = width))).getD fallback

theorem widthAxis_eq {d : ℕ} {k : BoxKey d} (unique : Function.Injective k.radius)
    (fallback j : Fin d) : widthAxis k fallback (k.radius j) = j := by
  unfold widthAxis
  cases hf : (List.finRange d).find? (fun i => decide (k.radius i = k.radius j)) with
  | none =>
      have hn := List.find?_eq_none.mp hf j (List.mem_finRange j)
      simp at hn
  | some i =>
      have hi := List.find?_some hf
      have hij : i = j := unique (by simpa using hi)
      simp [hij]

/-- Output-row axis map, exactly as in `pairpose(root, source)`. -/
def pairAxis {d : ℕ} (a b : Facet d) (root source : BoxKey d) (i : Fin d) : Fin d :=
  if i = a.axis then b.axis else widthAxis source b.axis (root.radius i)

/-- Sign of an apex displacement, including the normal displacement. -/
def BoxKey.offsetSign {d : ℕ} (k : BoxKey d) (i : Fin d) : ℤ :=
  Int.sign (k.apex i - k.centre i)

/-- Normal opposition and tangent apex offsets determine all row signs. -/
def pairSign {d : ℕ} (a b : Facet d) (root source : BoxKey d) (i : Fin d) : ℤ :=
  if i = a.axis then -a.normal * b.normal
  else root.offsetSign i * source.offsetSign (pairAxis a b root source i)

def pairNegative {d : ℕ} (a b : Facet d) (root source : BoxKey d) : Fin d → Bool :=
  fun i => decide (pairSign a b root source i < 0)

/-- The exact numerator tested for divisibility in the Python generator. -/
def pairNumerator {d : ℕ} (a b : Facet d) (root source : BoxKey d) : ScaledPoint d :=
  fun i => root.centre i - pairSign a b root source i *
    source.centre (pairAxis a b root source i)

/-- Defensive inverse checks make the returned finite row a genuine pose. -/
def PairReady {d : ℕ} (den : ℤ) (a b : Facet d) (root source : BoxKey d) : Prop :=
  Function.LeftInverse (pairAxis b a source root) (pairAxis a b root source) ∧
  Function.RightInverse (pairAxis b a source root) (pairAxis a b root source) ∧
  (∀ i, pairSign a b root source i = -1 ∨ pairSign a b root source i = 1) ∧
  ∀ i, den ∣ pairNumerator a b root source i

instance {d : ℕ} (den : ℤ) (a b : Facet d) (root source : BoxKey d) :
    Decidable (PairReady den a b root source) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A finite key pair produces zero or one integral registered pose. -/
def pairPose {d : ℕ} (den : ℤ) (a b : Facet d)
    (root source : BoxKey d) : Option (Pose d) :=
  if h : PairReady den a b root source then
    some ⟨⟨pairAxis a b root source, pairAxis b a source root, h.1, h.2.1⟩,
      pairNegative a b root source, fun i => pairNumerator a b root source i / den⟩
  else none

theorem pairAxis_eq_of_match {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (unique : Function.Injective source.radius) (haxis : p.perm a.axis = b.axis)
    (matchKey : root = p.boxKey den source) :
    pairAxis a b root source = p.perm := by
  funext i
  by_cases hi : i = a.axis
  · subst i
    simp [pairAxis, haxis]
  · have hw : root.radius i = source.radius (p.perm i) :=
      congrFun (congrArg BoxKey.radius matchKey) i
    simp only [pairAxis, if_neg hi, hw]
    exact widthAxis_eq unique b.axis (p.perm i)

theorem BoxKey.radius_injective_of_match {d : ℕ} {den : ℤ} {p : Pose d}
    {root source : BoxKey d} (unique : Function.Injective source.radius)
    (matchKey : root = p.boxKey den source) : Function.Injective root.radius := by
  intro i j hij
  apply p.perm.injective
  apply unique
  simpa [matchKey, Pose.boxKey] using hij

theorem pairAxis_reverse_eq_of_match {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (unique : Function.Injective source.radius) (haxis : p.perm a.axis = b.axis)
    (matchKey : root = p.boxKey den source) :
    pairAxis b a source root = p.perm.symm := by
  have root_unique := BoxKey.radius_injective_of_match unique matchKey
  funext i
  by_cases hi : i = b.axis
  · subst i
    simp [pairAxis, ← haxis]
  · have hw : source.radius i = root.radius (p.perm.symm i) := by
      simp [matchKey, Pose.boxKey]
    simp only [pairAxis, if_neg hi, hw]
    exact widthAxis_eq root_unique a.axis (p.perm.symm i)

theorem int_sign_sq {z : ℤ} (hz : z ≠ 0) : Int.sign z * Int.sign z = 1 := by
  rcases lt_or_gt_of_ne hz with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]

theorem pairSign_eq_of_match {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (asymmetric : source.Asymmetric) (shared : Shared p a b)
    (matchKey : root = p.boxKey den source) :
    pairSign a b root source = p.sign := by
  have haxes := pairAxis_eq_of_match asymmetric.1 shared.2.1 matchKey
  funext i
  by_cases hi : i = a.axis
  · subst i
    have hn := shared.2.2
    simp only [pairSign, if_pos rfl]
    cases ha : a.positive <;> cases hb : b.positive <;> cases hp : p.negative a.axis <;>
      simp [Facet.normal, Pose.sign, ha, hb, hp] at hn ⊢
  · have hoff : root.apex i - root.centre i =
        p.sign i * (source.apex (p.perm i) - source.centre (p.perm i)) := by
      rw [matchKey]
      simp only [Pose.boxKey, Pose.scaledPoint]
      ring
    simp only [pairSign, if_neg hi, haxes, BoxKey.offsetSign, hoff, Int.sign_mul]
    rw [mul_assoc, int_sign_sq (asymmetric.2 (p.perm i)), mul_one]
    cases hp : p.negative i <;> simp [Pose.sign, hp]

theorem pairNumerator_eq_of_match {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (asymmetric : source.Asymmetric) (shared : Shared p a b)
    (matchKey : root = p.boxKey den source) :
    pairNumerator a b root source = fun i => den * p.shift i := by
  have haxes := pairAxis_eq_of_match asymmetric.1 shared.2.1 matchKey
  have hsign := pairSign_eq_of_match asymmetric shared matchKey
  funext i
  simp only [pairNumerator, haxes, hsign]
  rw [matchKey]
  simp [Pose.boxKey, Pose.scaledPoint]

/-- The actual finite algorithm recovers the given pose, not merely an abstract
pose with the same signature. In particular its integrality test cannot omit it. -/
theorem pairPose_eq_some_of_match {d : ℕ} {den : ℤ} (den_ne : den ≠ 0)
    {p : Pose d} {a b : Facet d} {root source : BoxKey d}
    (asymmetric : source.Asymmetric) (shared : Shared p a b)
    (matchKey : root = p.boxKey den source) :
    pairPose den a b root source = some p := by
  have haxes := pairAxis_eq_of_match asymmetric.1 shared.2.1 matchKey
  have hinverse := pairAxis_reverse_eq_of_match asymmetric.1 shared.2.1 matchKey
  have hsign := pairSign_eq_of_match asymmetric shared matchKey
  have hnum := pairNumerator_eq_of_match asymmetric shared matchKey
  have hready : PairReady den a b root source := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp only [haxes, hinverse, Equiv.symm_apply_apply]
    · intro i
      simp only [haxes, hinverse, Equiv.apply_symm_apply]
    · intro i
      rw [hsign]
      cases hp : p.negative i <;> simp [Pose.sign, hp]
    · intro i
      rw [hnum]
      exact dvd_mul_right den (p.shift i)
  unfold pairPose
  rw [dif_pos hready]
  congr 1
  have hperm : (⟨pairAxis a b root source, pairAxis b a source root,
      hready.1, hready.2.1⟩ : Equiv.Perm (Fin d)) = p.perm := by
    apply Equiv.ext
    intro i
    exact congrFun haxes i
  have hnegative : pairNegative a b root source = p.negative := by
    funext i
    simp only [pairNegative, hsign]
    cases hp : p.negative i <;> simp [Pose.sign, hp]
  have hshift : (fun i => pairNumerator a b root source i / den) = p.shift := by
    funext i
    rw [hnum]
    exact Int.mul_ediv_cancel_left (p.shift i) den_ne
  cases p
  simp_all only [Pose.mk.injEq]

/-- Completeness enumerates every ordered facet/key pair, including pairs from
separate components. No precomputed row or purported survivor appears here. -/
def IndexedGeometry.generatedCandidates {d n : ℕ} (g : IndexedGeometry d n) :
    Finset (Pose d) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    (g.profile i).biUnion fun root => (g.profile j).biUnion fun source =>
      (pairPose g.denominator (g.facet i) (g.facet j) root source).toFinset

theorem IndexedGeometry.mem_generatedCandidates_of_match {d n : ℕ}
    {g : IndexedGeometry d n} (den_ne : g.denominator ≠ 0)
    {p : Pose d} {i j : Fin n} {root source : BoxKey d}
    (hroot : root ∈ g.profile i) (hsource : source ∈ g.profile j)
    (asymmetric : source.Asymmetric) (shared : Shared p (g.facet i) (g.facet j))
    (matchKey : root = p.boxKey g.denominator source) :
    p ∈ g.generatedCandidates := by
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨root, hroot, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨source, hsource, ?_⟩
  rw [pairPose_eq_some_of_match den_ne asymmetric shared matchKey]
  simp

#print axioms pairPose_eq_some_of_match
#print axioms IndexedGeometry.mem_generatedCandidates_of_match

/-- The full signature of an asymmetric key determines every registered pose. -/
theorem Pose.boxKey_injective_of_asymmetric {d : ℕ} {den : ℤ} (den_ne : den ≠ 0)
    {key : BoxKey d} (asymmetric : key.Asymmetric) :
    Function.Injective (fun p : Pose d => p.boxKey den key) := by
  intro p q he
  have hperm : p.perm = q.perm := by
    apply Equiv.ext
    intro i
    apply asymmetric.1
    exact congrFun (congrArg BoxKey.radius he) i
  have hnegative : p.negative = q.negative := by
    funext i
    have hc := congrFun (congrArg BoxKey.centre he) i
    have ha := congrFun (congrArg BoxKey.apex he) i
    have hn := asymmetric.2 (q.perm i)
    cases hp : p.negative i <;> cases hq : q.negative i <;> try rfl
    all_goals
      simp [Pose.boxKey, Pose.scaledPoint, Pose.sign, hp, hq, hperm] at hc ha
      omega
  have hshift : p.shift = q.shift := by
    funext i
    have hc := congrFun (congrArg BoxKey.centre he) i
    simp only [Pose.boxKey, Pose.scaledPoint, Pose.sign, hperm, hnegative] at hc
    exact mul_left_cancel₀ den_ne (by linarith)
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

/-- Width and offset asymmetry is invariant under registered key transport. -/
theorem Pose.boxKey_asymmetric {d : ℕ} (p : Pose d) (den : ℤ)
    {key : BoxKey d} (asymmetric : key.Asymmetric) : (p.boxKey den key).Asymmetric := by
  constructor
  · exact BoxKey.radius_injective_of_match asymmetric.1 rfl
  · intro i
    have hn := asymmetric.2 (p.perm i)
    cases hp : p.negative i <;>
      simp [Pose.boxKey, Pose.scaledPoint, Pose.sign, hp] <;> omega

/-- Elementary shape facts needed to reconstruct the box signature from its
literal vertices: one flat normal coordinate and an apex over the base. -/
def BoxKey.PlaneShape {d : ℕ} (axis : Fin d) (k : BoxKey d) : Prop :=
  k.radius axis = 0 ∧ k.apex axis ≠ k.centre axis ∧
  (∀ i, 0 ≤ k.radius i) ∧
  ∀ i, i ≠ axis → k.centre i - k.radius i ≤ k.apex i ∧
    k.apex i ≤ k.centre i + k.radius i

instance {d : ℕ} (axis : Fin d) (k : BoxKey d) : Decidable (k.PlaneShape axis) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Exact integer placement of the base plane on its owned unit facet. -/
def BoxKey.OnFacet {d : ℕ} (den : ℤ) (f : Facet d) (k : BoxKey d) : Prop :=
  k.PlaneShape f.axis ∧ 2 * k.centre f.axis = den * f.centre2 f.axis

instance {d : ℕ} (den : ℤ) (f : Facet d) (k : BoxKey d) :
    Decidable (k.OnFacet den f) := inferInstanceAs (Decidable (_ ∧ _))

theorem BoxKey.tangent_vertex_bounds {d : ℕ} {axis : Fin d} {k : BoxKey d}
    (shape : k.PlaneShape axis) {i : Fin d} (tangent : i ≠ axis)
    {v : ScaledPoint d} (hv : v ∈ k.literal.vertices) :
    k.centre i - k.radius i ≤ v i ∧ v i ≤ k.centre i + k.radius i := by
  rcases Finset.mem_insert.mp hv with rfl | hb
  · exact shape.2.2.2 i tangent
  · rcases Finset.mem_image.mp hb with ⟨bits, _, rfl⟩
    have hr := shape.2.2.1 i
    cases hbits : bits i <;> simp [BoxKey.corner, hbits] <;> omega

theorem BoxKey.lowerCorner_mem {d : ℕ} (k : BoxKey d) :
    k.corner (fun _ => false) ∈ k.literal.vertices :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)

theorem BoxKey.upperCorner_mem {d : ℕ} (k : BoxKey d) :
    k.corner (fun _ => true) ∈ k.literal.vertices :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)

/-- A common base plane plus literal equality recovers the entire signature.
The proof identifies the off-plane apex and the tangent coordinate extrema. -/
theorem BoxKey.eq_of_literal_eq {d : ℕ} {axis : Fin d} {root source : BoxKey d}
    (rootShape : root.PlaneShape axis) (sourceShape : source.PlaneShape axis)
    (commonPlane : root.centre axis = source.centre axis)
    (literal : root.literal = source.literal) : root = source := by
  have hvertices := congrArg VertexKey.vertices literal
  have hbump := congrArg VertexKey.bump literal
  have hapex : root.apex = source.apex := by
    have hm : root.apex ∈ source.literal.vertices := by
      rw [← hvertices]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hm with he | hm
    · exact he
    · rcases Finset.mem_image.mp hm with ⟨bits, _, he⟩
      have hi := congrFun he axis
      simp [BoxKey.corner, sourceShape.1] at hi
      exact (rootShape.2.1 (commonPlane.trans hi).symm).elim
  have hextrema : ∀ i, root.centre i = source.centre i ∧ root.radius i = source.radius i := by
    intro i
    by_cases hi : i = axis
    · subst i
      exact ⟨commonPlane, rootShape.1.trans sourceShape.1.symm⟩
    · have hrl : root.corner (fun _ => false) ∈ source.literal.vertices := by
        rw [← hvertices]
        exact root.lowerCorner_mem
      have hru : root.corner (fun _ => true) ∈ source.literal.vertices := by
        rw [← hvertices]
        exact root.upperCorner_mem
      have hsl : source.corner (fun _ => false) ∈ root.literal.vertices := by
        rw [hvertices]
        exact source.lowerCorner_mem
      have hsu : source.corner (fun _ => true) ∈ root.literal.vertices := by
        rw [hvertices]
        exact source.upperCorner_mem
      have h1 := (BoxKey.tangent_vertex_bounds sourceShape hi hrl).1
      have h2 := (BoxKey.tangent_vertex_bounds sourceShape hi hru).2
      have h3 := (BoxKey.tangent_vertex_bounds rootShape hi hsl).1
      have h4 := (BoxKey.tangent_vertex_bounds rootShape hi hsu).2
      simp [BoxKey.corner] at h1 h2 h3 h4
      constructor <;> omega
  have hcentre : root.centre = source.centre := funext fun i => (hextrema i).1
  have hradius : root.radius = source.radius := funext fun i => (hextrema i).2
  cases root
  cases source
  simp_all only [BoxKey.literal, BoxKey.mk.injEq, VertexKey.mk.injEq]

/-- The shape hypotheses are coordinate facts preserved by a signed pose. -/
theorem Pose.boxKey_planeShape {d : ℕ} {p : Pose d} (den : ℤ)
    {a b : Facet d} {source : BoxKey d} (axes : p.perm a.axis = b.axis)
    (shape : source.PlaneShape b.axis) : (p.boxKey den source).PlaneShape a.axis := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Pose.boxKey, axes] using shape.1
  · have hn := shape.2.1
    cases hp : p.negative a.axis <;>
      simp [Pose.boxKey, Pose.scaledPoint, Pose.sign, hp, axes] <;> omega
  · intro i
    exact shape.2.2.1 (p.perm i)
  · intro i hi
    have hsource : p.perm i ≠ b.axis := by
      rw [← axes]
      exact fun h => hi (p.perm.injective h)
    have hb := shape.2.2.2 (p.perm i) hsource
    cases hp : p.negative i <;>
      simp [Pose.boxKey, Pose.scaledPoint, Pose.sign, hp] <;> constructor <;> omega

/-- Shared facets transport the base plane exactly, without floating point. -/
theorem BoxKey.commonPlane_of_shared {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (rootOn : root.OnFacet den a) (sourceOn : source.OnFacet den b)
    (shared : Shared p a b) :
    root.centre a.axis = (p.boxKey den source).centre a.axis := by
  have hc := congrFun shared.1 a.axis
  simp only [Pose.scaledPoint, shared.2.1] at hc
  change root.centre a.axis =
    p.sign a.axis * source.centre (p.perm a.axis) + den * p.shift a.axis
  rw [shared.2.1]
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  calc
    2 * root.centre a.axis = den * a.centre2 a.axis := rootOn.2
    _ = den * (p.sign a.axis * b.centre2 b.axis + 2 * p.shift a.axis) := by rw [hc]
    _ = p.sign a.axis * (den * b.centre2 b.axis) +
        2 * (den * p.shift a.axis) := by ring
    _ = p.sign a.axis * (2 * source.centre b.axis) +
        2 * (den * p.shift a.axis) := by rw [← sourceOn.2]
    _ = 2 * (p.sign a.axis * source.centre b.axis + den * p.shift a.axis) := by ring

/-- Literal equality on two opposed registered facets yields full-key equality. -/
theorem BoxKey.eq_pose_of_literal_match {d : ℕ} {den : ℤ} {p : Pose d}
    {a b : Facet d} {root source : BoxKey d}
    (rootOn : root.OnFacet den a) (sourceOn : source.OnFacet den b)
    (shared : Shared p a b) (literal : root.literal = p.key den source.literal) :
    root = p.boxKey den source := by
  apply BoxKey.eq_of_literal_eq rootOn.1
    (Pose.boxKey_planeShape den shared.2.1 sourceOn.1)
    (BoxKey.commonPlane_of_shared rootOn sourceOn shared)
  rw [p.boxKey_literal]
  exact literal

/-- Every registered literal-profile contact is generated, assuming checked
nonempty profiles and elementary per-key shape/asymmetry facts. The candidate
list is never a premise. This still does not register arbitrary isometries. -/
theorem IndexedGeometry.legalContact_mem_generatedCandidates {d n : ℕ}
    {g : IndexedGeometry d n} (den_ne : g.denominator ≠ 0)
    (nonempty : ∀ i, (g.profile i).Nonempty)
    (valid : ∀ i k, k ∈ g.profile i → k.OnFacet g.denominator (g.facet i))
    (asymmetric : ∀ i k, k ∈ g.profile i → k.Asymmetric)
    {p : Pose d} (legal : g.LegalContact p) : p ∈ g.generatedCandidates := by
  obtain ⟨i, j, shared⟩ := legal.2.1
  obtain ⟨root, hroot⟩ := nonempty i
  have hmem : root.literal ∈ (g.profile i).image BoxKey.literal :=
    Finset.mem_image.mpr ⟨root, hroot, rfl⟩
  rw [legal.2.2 i j shared] at hmem
  rcases Finset.mem_image.mp hmem with ⟨lit, hlit, heq⟩
  rcases Finset.mem_image.mp hlit with ⟨source, hsource, rfl⟩
  exact IndexedGeometry.mem_generatedCandidates_of_match den_ne hroot hsource
    (asymmetric j source hsource) shared
    (BoxKey.eq_pose_of_literal_match (valid i root hroot) (valid j source hsource)
      shared heq.symm)

#print axioms Pose.boxKey_injective_of_asymmetric
#print axioms BoxKey.eq_of_literal_eq
#print axioms BoxKey.eq_pose_of_literal_match
#print axioms IndexedGeometry.legalContact_mem_generatedCandidates

end SparseMonotiles.Contact
