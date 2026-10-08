module
public import T7PolarityIndexing
public import T7PackedReplayBase
@[expose] public section
namespace SparseMonotiles.T7MatchedKeyReduction
open Contact CarrierHierarchy ContactInverseReuse T7KeyIndexing T7PolarityIndexing
set_option maxRecDepth 100000

/-- Keep the actual matched box key, rather than forgetting it after invoking
pairPose. The inverse branch exchanges the same two matched keys. -/
theorem legal_exists_bump_dent_match_or_inverse {p : Pose 7}
    (legal : IndexedData7.geometry.LegalContact p) :
    ∃ a b : Fin 1024,
      (generatorIndexingT7.key a).bump = true ∧
      (generatorIndexingT7.key b).bump = false ∧
      (generatorIndexingT7.key a = p.boxKey IndexedData7.geometry.denominator
          (generatorIndexingT7.key b) ∨
       generatorIndexingT7.key a = (inversePose p).boxKey IndexedData7.geometry.denominator
          (generatorIndexingT7.key b)) := by
  obtain ⟨i, j, root, source, hroot, hsource, shared, literal, polarity⟩ :=
    IndexedGeometry.legalContact_exists_matched_opposite_keys
      (fun i => (profile7_checked i).1) legal
  cases hr : root.bump with
  | false =>
      have hs : source.bump = true := by
        cases h : source.bump <;> simp_all
      have inverse_literal : source.literal =
          (inversePose p).key IndexedData7.geometry.denominator root.literal := by
        rw [literal, inversePose_key_key]
      have matched := BoxKey.eq_pose_of_literal_match
        (((profile7_checked j).2 source hsource).1)
        (((profile7_checked i).2 root hroot).1) (shared_inversePose shared) inverse_literal
      obtain ⟨a, _, har⟩ := generatorIndexingT7.covers hsource
      obtain ⟨b, _, hbs⟩ := generatorIndexingT7.covers hroot
      exact ⟨a, b, by rw [har]; exact hs, by rw [hbs]; exact hr,
        Or.inr (by simpa only [har, hbs] using matched)⟩
  | true =>
      have hs : source.bump = false := by
        cases h : source.bump <;> simp_all
      have matched := BoxKey.eq_pose_of_literal_match
        (((profile7_checked i).2 root hroot).1)
        (((profile7_checked j).2 source hsource).1) shared literal
      obtain ⟨a, _, har⟩ := generatorIndexingT7.covers hroot
      obtain ⟨b, _, hbs⟩ := generatorIndexingT7.covers hsource
      exact ⟨a, b, by rw [har]; exact hr, by rw [hbs]; exact hs,
        Or.inl (by simpa only [har, hbs] using matched)⟩

/-- Exact 512 by 512 matched-key obligation. No computation of pairPose is
required: only actual key matches extracted from the legal physical contact. -/
theorem contact_mem_M7_of_512_matched_key_classifications
    (hpairs : ∀ (a b : Fin 512) (p : Pose 7),
      generatorIndexingT7.key (bumpIndex a) =
        p.boxKey IndexedData7.geometry.denominator (generatorIndexingT7.key (dentIndex b)) →
      IndexedData7.geometry.LegalContact p → p ∈ M7)
    {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 := by
  obtain ⟨a,b,ha,hb,matched⟩ := legal_exists_bump_dent_match_or_inverse legal
  have classify : ∀ q : Pose 7,
      generatorIndexingT7.key a = q.boxKey IndexedData7.geometry.denominator
        (generatorIndexingT7.key b) → IndexedData7.geometry.LegalContact q → q ∈ M7 := by
    intro q hm hq
    apply hpairs (rank a) (rank b) q ?_ hq
    simpa only [bumpIndex_covers ha, dentIndex_covers hb] using hm
  rcases matched with hm | hm
  · exact classify p hm legal
  · exact (M7_inversePose_iff p).mpr
      (classify (inversePose p) hm (legalContact_inversePose legal))

/-- Every original indexed key is asymmetric, using its certified profile owner. -/
theorem indexed_key_asymmetric (b : Fin 1024) : (generatorIndexingT7.key b).Asymmetric :=
  (((profile7_checked (generatorIndexingT7.facet b)).2 _ (source_mem_profile b)).2.1)

noncomputable def keyMatchCheck (a b : Fin 1024) (p : Pose 7) : Bool :=
  decide (generatorIndexingT7.key a =
    p.boxKey IndexedData7.geometry.denominator (generatorIndexingT7.key b))

/-- A checked full box-key match uniquely binds the whole registered pose.
This avoids replaying width-axis searches, inverse tests and divisibility. -/
theorem eq_of_checked_match {a b : Fin 1024} {p q : Pose 7}
    (checked : keyMatchCheck a b q = true)
    (matched : generatorIndexingT7.key a =
      p.boxKey IndexedData7.geometry.denominator (generatorIndexingT7.key b)) : p = q := by
  have hq : generatorIndexingT7.key a =
      q.boxKey IndexedData7.geometry.denominator (generatorIndexingT7.key b) :=
    of_decide_eq_true checked
  exact Pose.boxKey_injective_of_asymmetric
    (by decide : IndexedData7.geometry.denominator ≠ 0) (indexed_key_asymmetric b)
    (matched.symm.trans hq)

noncomputable def matchedDirectCheck (a b : Fin 1024) (r : PackedReplay.PackedRow) : Bool :=
  keyMatchCheck a b (PackedReplay.decodePose r.code) && PackedReplay.rowCheck r

theorem classify_from_matched_direct {a b : Fin 1024} {r : PackedReplay.PackedRow}
    (checked : matchedDirectCheck a b r = true) (p : Pose 7)
    (matched : generatorIndexingT7.key a =
      p.boxKey IndexedData7.geometry.denominator (generatorIndexingT7.key b))
    (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 := by
  have hc : keyMatchCheck a b (PackedReplay.decodePose r.code) = true ∧
      PackedReplay.rowCheck r = true := by
    simpa only [matchedDirectCheck, Bool.and_eq_true_iff] using checked
  have he := eq_of_checked_match hc.1 matched
  exact he ▸ PackedReplay.certCheck_sound hc.2 (he ▸ legal)

#print axioms legal_exists_bump_dent_match_or_inverse
#print axioms contact_mem_M7_of_512_matched_key_classifications
#print axioms indexed_key_asymmetric
#print axioms eq_of_checked_match
#print axioms classify_from_matched_direct
end SparseMonotiles.T7MatchedKeyReduction
