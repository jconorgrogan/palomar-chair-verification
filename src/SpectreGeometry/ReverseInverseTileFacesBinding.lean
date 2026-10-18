module

public import SpectreGeometry.ReverseInverseTileFacesReal
public import SpectreGeometry.DevelopedLiteralBody

@[expose] public section


/-! Exact transfer of the checked raw H/T common-face certificates to the
actual developed target triangles used by the inverse deformation. -/
namespace SpectreGeometry.ReverseInverseTile
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP SpectreClusters.DeformedLiteralBinding
open Deformation ReverseClusterTriangulation

theorem gridRotation_injective (k : Turn) : Function.Injective (gridRotation k) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases k <;> apply Prod.ext <;> simp [gridRotation] at hx hy ⊢ <;> linarith

theorem gridEmbeddingLinear_injective : Function.Injective gridEmbeddingLinear := by
  intro p q h
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [gridEmbeddingLinear] at hx hy
  have he : p.1=q.1 := by nlinarith
  exact Prod.ext he (by rw [he] at hy; linarith)

theorem gridReflectionLinear_injective : Function.Injective gridReflectionLinear := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [gridReflectionLinear] at hx hy
  exact Prod.ext hx (by rw [hx] at hy; linarith)

theorem literalTargetAffine_injective (k : Fin 12) : Function.Injective (literalTargetAffine k) := by
  intro p q h
  apply gridRotation_injective (literalTurn k)
  apply add_left_cancel (a := integerPoint (reflectPoint (deformedOffset k)))
  exact gridReflectionLinear_injective (gridEmbeddingLinear_injective h)

def developedTriangleVertices (k i : Fin 12) : Set RealPoint :=
  range (fun v : Fin 3 => realDeformedVertex k (triangleIndex i v))

theorem canonicalTriangle_vertices (kind : HTKind) (i : Fin 12) :
    integerVertexSet ((targetVertexLists kind).getD i.val []) =
      range (fun v : Fin 3 => integerPoint (canonicalVertex kind (triangleIndex i v))) := by
  rw [targetVertexLists_get]
  ext p
  simp only [canonicalTriangle,integerVertexSet,mem_image,mem_setOf_eq,List.mem_cons,List.not_mem_nil,
    or_false,mem_range]
  constructor
  · rintro ⟨q,(rfl|rfl|rfl),rfl⟩
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨1,rfl⟩
  · rintro ⟨v,rfl⟩
    fin_cases v <;> simp

theorem literalTargetAffine_image_vertices (k i : Fin 12) :
    literalTargetAffine k '' integerVertexSet ((targetVertexLists (literalKind k)).getD i.val []) =
      developedTriangleVertices k i := by
  rw [canonicalTriangle_vertices]
  ext p
  constructor
  · rintro ⟨q,⟨v,rfl⟩,rfl⟩
    exact ⟨v,(literalTargetAffine_vertex k (triangleIndex i v)).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨_,⟨v,rfl⟩,literalTargetAffine_vertex k (triangleIndex i v)⟩

theorem targetTriangles_common_face (k i j : Fin 12) :
    targetTriangle k i ∩ targetTriangle k j =
      convexHull ℝ (developedTriangleVertices k i ∩ developedTriangleVertices k j) := by
  by_cases hij : i=j
  · subst j
    simp only [Set.inter_self]
    rfl
  let ii : Fin (canonicalPackets (literalKind k)).length := ⟨i.val,by rw [canonicalPackets_length]; exact i.isLt⟩
  let jj : Fin (canonicalPackets (literalKind k)).length := ⟨j.val,by rw [canonicalPackets_length]; exact j.isLt⟩
  have hne : ii ≠ jj := fun h => hij (Fin.ext (congrArg Fin.val h))
  have hf := (canonicalPackets_have_faces (literalKind k) ii jj hne).1
  have hf' : integerHull ((targetVertexLists (literalKind k)).getD i.val []) ∩
      integerHull ((targetVertexLists (literalKind k)).getD j.val []) =
      convexHull ℝ (integerVertexSet ((targetVertexLists (literalKind k)).getD i.val []) ∩
        integerVertexSet ((targetVertexLists (literalKind k)).getD j.val [])) := by
    simpa only [ii,jj,canonicalPackets_getD,canonicalPacket] using hf
  have h := congrArg (fun s => literalTargetAffine k '' s) hf'
  rw [Set.image_inter (literalTargetAffine_injective k),
    literalTargetAffine_image_triangle,literalTargetAffine_image_triangle,
    (literalTargetAffine k).image_convexHull,
    Set.image_inter (literalTargetAffine_injective k),
    literalTargetAffine_image_vertices,literalTargetAffine_image_vertices] at h
  exact h

end
end SpectreGeometry.ReverseInverseTile
