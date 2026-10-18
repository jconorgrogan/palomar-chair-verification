module

public import SpectreGeometry.ReverseLocalStarStructuralSoundness

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

def CommonFaces (ts : List (List Point)) : Prop :=
  ∀ a ∈ ts, ∀ b ∈ ts, integerHull a ∩ integerHull b =
    convexHull ℝ (integerVertexSet a ∩ integerVertexSet b)

theorem commonFaces_of_packets (ps : List PolygonPacket) (h : FamilyHasFaces ps) :
    CommonFaces (ps.map PolygonPacket.vertices) := by
  rintro a ha b hb
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hq
  by_cases hij : i=j
  · subst j
    simp only [inter_self]
    rfl
  · have hh := (h i j hij).1
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem j.isLt,Option.getD_some,List.get_eq_getElem] using hh

theorem commonFaces_of_normalizedStructural (ts : List (List Point))
    (h : CommonFaces (normalizedStructural ts)) : CommonFaces ts := by
  intro a ha b hb
  have hma : sortB pointLE a ∈ normalizedStructural ts :=
    (sortB_perm triangleLE _).mem_iff.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hmb : sortB pointLE b ∈ normalizedStructural ts :=
    (sortB_perm triangleLE _).mem_iff.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩)
  have hh := h _ hma _ hmb
  simpa only [integerHull_perm (sortB_perm pointLE a),integerHull_perm (sortB_perm pointLE b),
    integerVertexSet_perm (sortB_perm pointLE a),integerVertexSet_perm (sortB_perm pointLE b)] using hh

theorem commonFaces_normalizedStructural (ts : List (List Point))
    (h : CommonFaces ts) : CommonFaces (normalizedStructural ts) := by
  intro a ha b hb
  obtain ⟨a',ha',rfl⟩ := List.mem_map.mp ((sortB_perm triangleLE _).mem_iff.mp ha)
  obtain ⟨b',hb',rfl⟩ := List.mem_map.mp ((sortB_perm triangleLE _).mem_iff.mp hb)
  simpa only [integerHull_perm (sortB_perm pointLE a'),integerHull_perm (sortB_perm pointLE b'),
    integerVertexSet_perm (sortB_perm pointLE a'),integerVertexSet_perm (sortB_perm pointLE b')] using h a' ha' b' hb'

theorem integerVertexSet_map_affine (f : Point → Point) (A : RealPoint →ᵃ[ℝ] RealPoint)
    (hf : ∀ p, integerPoint (f p)=A (integerPoint p)) (vs : List Point) :
    integerVertexSet (vs.map f) = A '' integerVertexSet vs := by
  ext x
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact ⟨integerPoint p,⟨p,hp,rfl⟩,(hf p).symm⟩
  · rintro ⟨q,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨f p,List.mem_map.mpr ⟨p,hp,rfl⟩,hf p⟩

theorem integerHull_map_affine (f : Point → Point) (A : RealPoint →ᵃ[ℝ] RealPoint)
    (hf : ∀ p, integerPoint (f p)=A (integerPoint p)) (vs : List Point) :
    integerHull (vs.map f) = A '' integerHull vs := by
  change convexHull ℝ (integerVertexSet (vs.map f)) = A '' convexHull ℝ (integerVertexSet vs)
  rw [integerVertexSet_map_affine f A hf,←A.image_convexHull]

/-- Pull back exact common-face equalities through any injective affine frame,
including the integer rotations and the certificate's factor-1000 scaling. -/
theorem commonFaces_of_affine_map (ts : List (List Point)) (f : Point → Point)
    (A : RealPoint →ᵃ[ℝ] RealPoint) (hA : Function.Injective A)
    (hf : ∀ p, integerPoint (f p)=A (integerPoint p))
    (h : CommonFaces (ts.map (fun t => t.map f))) : CommonFaces ts := by
  intro a ha b hb
  have hh := h _ (List.mem_map.mpr ⟨a,ha,rfl⟩) _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
  rw [integerHull_map_affine f A hf,integerHull_map_affine f A hf,
    integerVertexSet_map_affine f A hf,integerVertexSet_map_affine f A hf,
    ←Set.image_inter hA,←Set.image_inter hA,←A.image_convexHull] at hh
  exact hA.image_injective hh

/-- The finite occurrence equality transports all closed common-face
intersections, not just neighborhood coverage. Vertex correspondence is a
separate obligation when using these intersections for inverse agreement. -/
theorem occurrenceStructural_commonFaces (ts : List (List Point)) (code : Nat)
    (hc : occurrenceStructuralB ts code = true)
    (h : CommonFaces (canonicalStars.getD (code/6) [])) : CommonFaces ts := by
  have hh : normalizedStructural (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
      normalizedStructural (canonicalStars.getD (code/6) []) := by
    have he : code<744 ∧
        normalizedStructural (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
          normalizedStructural (canonicalStars.getD (code/6) []) := by
      simpa only [occurrenceStructuralB,rotatedStar,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using hc
    exact he.2
  have hnorm := commonFaces_normalizedStructural _ h
  rw [←hh] at hnorm
  have hrot := commonFaces_of_normalizedStructural _ hnorm
  exact commonFaces_of_affine_map ts (SpectreClusters.rotate ⟨code%6,Nat.mod_lt _ (by decide)⟩)
    (gridRotationLinear _).toAffineMap (gridTurnHomeomorph _).injective
    (integerPoint_rotate _) hrot

end
end SpectreGeometry.ReverseLocalStarOccurrences
