module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk0

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk0_aligned : ∀ k ∈ keys5Chunk0,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, IndexedData5.key0, by decide, canonicalPose5_0, canonicalMatch5_0, indexedKeyDecode5_0⟩
  · exact ⟨⟨0, by decide⟩, IndexedData5.key1, by decide, canonicalPose5_1, canonicalMatch5_1, indexedKeyDecode5_1⟩
  · exact ⟨⟨0, by decide⟩, IndexedData5.key2, by decide, canonicalPose5_2, canonicalMatch5_2, indexedKeyDecode5_2⟩
  · exact ⟨⟨0, by decide⟩, IndexedData5.key3, by decide, canonicalPose5_3, canonicalMatch5_3, indexedKeyDecode5_3⟩
  · exact ⟨⟨1, by decide⟩, IndexedData5.key4, by decide, canonicalPose5_4, canonicalMatch5_4, indexedKeyDecode5_4⟩
  · exact ⟨⟨2, by decide⟩, IndexedData5.key5, by decide, canonicalPose5_5, canonicalMatch5_5, indexedKeyDecode5_5⟩
  · exact ⟨⟨3, by decide⟩, IndexedData5.key6, by decide, canonicalPose5_6, canonicalMatch5_6, indexedKeyDecode5_6⟩
  · exact ⟨⟨4, by decide⟩, IndexedData5.key7, by decide, canonicalPose5_7, canonicalMatch5_7, indexedKeyDecode5_7⟩
  · exact ⟨⟨5, by decide⟩, IndexedData5.key8, by decide, canonicalPose5_8, canonicalMatch5_8, indexedKeyDecode5_8⟩
  · exact ⟨⟨6, by decide⟩, IndexedData5.key9, by decide, canonicalPose5_9, canonicalMatch5_9, indexedKeyDecode5_9⟩
  · exact ⟨⟨7, by decide⟩, IndexedData5.key10, by decide, canonicalPose5_10, canonicalMatch5_10, indexedKeyDecode5_10⟩
  · exact ⟨⟨8, by decide⟩, IndexedData5.key11, by decide, canonicalPose5_11, canonicalMatch5_11, indexedKeyDecode5_11⟩
  · exact ⟨⟨9, by decide⟩, IndexedData5.key12, by decide, canonicalPose5_12, canonicalMatch5_12, indexedKeyDecode5_12⟩
  · exact ⟨⟨9, by decide⟩, IndexedData5.key13, by decide, canonicalPose5_13, canonicalMatch5_13, indexedKeyDecode5_13⟩
  · exact ⟨⟨9, by decide⟩, IndexedData5.key14, by decide, canonicalPose5_14, canonicalMatch5_14, indexedKeyDecode5_14⟩
  · exact ⟨⟨9, by decide⟩, IndexedData5.key15, by decide, canonicalPose5_15, canonicalMatch5_15, indexedKeyDecode5_15⟩
  · exact ⟨⟨10, by decide⟩, IndexedData5.key16, by decide, canonicalPose5_16, canonicalMatch5_16, indexedKeyDecode5_16⟩
  · exact ⟨⟨11, by decide⟩, IndexedData5.key17, by decide, canonicalPose5_17, canonicalMatch5_17, indexedKeyDecode5_17⟩
  · exact ⟨⟨12, by decide⟩, IndexedData5.key18, by decide, canonicalPose5_18, canonicalMatch5_18, indexedKeyDecode5_18⟩
  · exact ⟨⟨13, by decide⟩, IndexedData5.key19, by decide, canonicalPose5_19, canonicalMatch5_19, indexedKeyDecode5_19⟩
  · exact ⟨⟨13, by decide⟩, IndexedData5.key20, by decide, canonicalPose5_20, canonicalMatch5_20, indexedKeyDecode5_20⟩
  · exact ⟨⟨13, by decide⟩, IndexedData5.key21, by decide, canonicalPose5_21, canonicalMatch5_21, indexedKeyDecode5_21⟩
  · exact ⟨⟨13, by decide⟩, IndexedData5.key22, by decide, canonicalPose5_22, canonicalMatch5_22, indexedKeyDecode5_22⟩
  · exact ⟨⟨14, by decide⟩, IndexedData5.key23, by decide, canonicalPose5_23, canonicalMatch5_23, indexedKeyDecode5_23⟩
  · exact ⟨⟨15, by decide⟩, IndexedData5.key24, by decide, canonicalPose5_24, canonicalMatch5_24, indexedKeyDecode5_24⟩
  · exact ⟨⟨16, by decide⟩, IndexedData5.key25, by decide, canonicalPose5_25, canonicalMatch5_25, indexedKeyDecode5_25⟩
  · exact ⟨⟨16, by decide⟩, IndexedData5.key26, by decide, canonicalPose5_26, canonicalMatch5_26, indexedKeyDecode5_26⟩
  · exact ⟨⟨16, by decide⟩, IndexedData5.key27, by decide, canonicalPose5_27, canonicalMatch5_27, indexedKeyDecode5_27⟩
  · exact ⟨⟨16, by decide⟩, IndexedData5.key28, by decide, canonicalPose5_28, canonicalMatch5_28, indexedKeyDecode5_28⟩
  · exact ⟨⟨17, by decide⟩, IndexedData5.key29, by decide, canonicalPose5_29, canonicalMatch5_29, indexedKeyDecode5_29⟩
  · exact ⟨⟨18, by decide⟩, IndexedData5.key30, by decide, canonicalPose5_30, canonicalMatch5_30, indexedKeyDecode5_30⟩
  · exact ⟨⟨19, by decide⟩, IndexedData5.key31, by decide, canonicalPose5_31, canonicalMatch5_31, indexedKeyDecode5_31⟩

#print axioms keys5Chunk0_aligned

end SparseMonotiles.Canonical
