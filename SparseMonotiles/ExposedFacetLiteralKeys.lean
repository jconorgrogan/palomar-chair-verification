module

public import SparseMonotiles.ExposedFacetLiteralKey5Chunk0
public import SparseMonotiles.ExposedFacetLiteralKey5Chunk1
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk0
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk1
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk2
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk3
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk4
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk5
public import SparseMonotiles.ExposedFacetLiteralKey7Chunk6

@[expose] public section

/-! Every indexed exposed facet carries an actual literal key.
Each witness reuses an existing checked key decode and append membership;
no geometric data equality is inferred from profile nonemptiness alone. -/
namespace SparseMonotiles
open Contact Canonical

theorem T5_indexed_facet_has_literal_key (i : Fin 160) :
    ∃ b ∈ IndexedData5.geometry.profile i, b.toKeyData 19200 ∈ keys5 := by
  by_cases h0 : i.val < 128
  · have h := exposedFacetLiteralKey5Chunk0 ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 160)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  have h := exposedFacetLiteralKey5Chunk1 ⟨i.val-128,by omega⟩
  have he : (⟨128+(i.val-128),by omega⟩ : Fin 160)=i := by
    apply Fin.ext
    dsimp
    omega
  exact he ▸ h

#print axioms T5_indexed_facet_has_literal_key

theorem T7_indexed_facet_has_literal_key (i : Fin 896) :
    ∃ b ∈ IndexedData7.geometry.profile i, b.toKeyData 188160 ∈ keys7 := by
  by_cases h0 : i.val < 128
  · have h := exposedFacetLiteralKey7Chunk0 ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h1 : i.val < 256
  · have h := exposedFacetLiteralKey7Chunk1 ⟨i.val-128,by omega⟩
    have he : (⟨128+(i.val-128),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h2 : i.val < 384
  · have h := exposedFacetLiteralKey7Chunk2 ⟨i.val-256,by omega⟩
    have he : (⟨256+(i.val-256),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h3 : i.val < 512
  · have h := exposedFacetLiteralKey7Chunk3 ⟨i.val-384,by omega⟩
    have he : (⟨384+(i.val-384),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h4 : i.val < 640
  · have h := exposedFacetLiteralKey7Chunk4 ⟨i.val-512,by omega⟩
    have he : (⟨512+(i.val-512),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h5 : i.val < 768
  · have h := exposedFacetLiteralKey7Chunk5 ⟨i.val-640,by omega⟩
    have he : (⟨640+(i.val-640),by omega⟩ : Fin 896)=i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  have h := exposedFacetLiteralKey7Chunk6 ⟨i.val-768,by omega⟩
  have he : (⟨768+(i.val-768),by omega⟩ : Fin 896)=i := by
    apply Fin.ext
    dsimp
    omega
  exact he ▸ h

#print axioms T7_indexed_facet_has_literal_key

end SparseMonotiles
