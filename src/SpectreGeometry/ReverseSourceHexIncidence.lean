module

public import SpectreGeometry.ReverseSourceHexSegments
public import SpectreGeometry.ReverseClosedCoverStars
public import SpectreFinite.HexRotation

@[expose] public section


/-! Exact incidence classification for the integer-centered source hexagons:
cell interiors, relative-open edges, and elementary three-cell vertices. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreFinite.HexSearch

theorem sourceHexCornerAt_mem_center (c : ℤ × ℤ) (d : Fin 6) :
    sourceHexCornerAt c d ∈ sourceHexCarrier c := by
  simp only [sourceHexCarrier,sourceHexCornerAt,Set.mem_ofPred_eq,add_sub_cancel_left]
  fin_cases d <;> norm_num [sourceHexCorner,sourceHexOffset]

theorem sourceHexCornerAt_mem_neighbor_iff (c : ℤ × ℤ) (d e : Fin 6) :
    sourceHexCornerAt c (d+1) ∈ sourceHexCarrier (sourceHexNeighbor c e) ↔
      e = d ∨ e = d+1 := by
  simp only [sourceHexCarrier,sourceHexCornerAt,sourceHexNeighbor,Set.mem_ofPred_eq,
    Int.cast_add]
  have hx : (c.1:ℝ)+(sourceHexCorner (d+1)).1-((c.1:ℝ)+(SpectreFinite.direction e).1) =
      (sourceHexCorner (d+1)).1-(SpectreFinite.direction e).1 := by ring
  have hy : (c.2:ℝ)+(sourceHexCorner (d+1)).2-((c.2:ℝ)+(SpectreFinite.direction e).2) =
      (sourceHexCorner (d+1)).2-(SpectreFinite.direction e).2 := by ring
  rw [hx,hy]
  fin_cases d <;> fin_cases e <;>
    norm_num [sourceHexCorner,sourceHexOffset,SpectreFinite.direction]

/-- Each corner belongs to exactly the intended elementary neighboring triple. -/
theorem sourceHexCornerAt_incident_iff (c z : ℤ × ℤ) (d : Fin 6) :
    sourceHexCornerAt c (d+1) ∈ sourceHexCarrier z ↔
      z = c ∨ z = sourceHexNeighbor c d ∨ z = sourceHexNeighbor c (d+1) := by
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact Or.inl hzc
    · obtain ⟨e,rfl⟩ := sourceHex_intersection_neighbor hzc
        ⟨sourceHexCornerAt c (d+1),sourceHexCornerAt_mem_center c (d+1),hz⟩
      rcases (sourceHexCornerAt_mem_neighbor_iff c d e).mp hz with he | he
      · exact Or.inr (Or.inl (by rw [he]))
      · exact Or.inr (Or.inr (by rw [he]))
  · intro hz
    rcases hz with hz | hz | hz
    · rw [hz]
      exact sourceHexCornerAt_mem_center c (d+1)
    · rw [hz]
      exact (sourceHexCornerAt_mem_neighbor_iff c d d).mpr (Or.inl rfl)
    · rw [hz]
      exact (sourceHexCornerAt_mem_neighbor_iff c d (d+1)).mpr (Or.inr rfl)

set_option maxHeartbeats 400000 in
/-- A third distinct neighboring carrier can meet a common edge only at an endpoint. -/
theorem sourceHex_third_neighbor_at_endpoint (c : ℤ × ℤ) (d e : Fin 6)
    (p : ℝ × ℝ) (hne : e ≠ d)
    (h0 : p ∈ sourceHexCarrier c)
    (hd : p ∈ sourceHexCarrier (sourceHexNeighbor c d))
    (he : p ∈ sourceHexCarrier (sourceHexNeighbor c e)) :
    p = sourceHexCornerAt c d ∨ p = sourceHexCornerAt c (d+1) := by
  fin_cases d <;> fin_cases e <;> norm_num at hne
  all_goals
    rcases h0 with ⟨h01,h02,h03,h04,h05,h06⟩
    rcases hd with ⟨hd1,hd2,hd3,hd4,hd5,hd6⟩
    rcases he with ⟨he1,he2,he3,he4,he5,he6⟩
    norm_num [sourceHexNeighbor,SpectreFinite.direction,Int.cast_add] at h01 h02 h03 h04 h05 h06 hd1 hd2 hd3 hd4 hd5 hd6 he1 he2 he3 he4 he5 he6
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · right; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · left; apply Prod.ext <;> norm_num [sourceHexCornerAt,sourceHexCorner] <;> linarith

/-- Nonendpoint points of a common source edge lie in exactly its two carriers. -/
theorem sourceHex_edge_incident_iff (c z : ℤ × ℤ) (d : Fin 6) (p : ℝ × ℝ)
    (hc : p ∈ sourceHexCarrier c)
    (hd : p ∈ sourceHexCarrier (sourceHexNeighbor c d))
    (hleft : p ≠ sourceHexCornerAt c d) (hright : p ≠ sourceHexCornerAt c (d+1)) :
    p ∈ sourceHexCarrier z ↔ z = c ∨ z = sourceHexNeighbor c d := by
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact Or.inl hzc
    obtain ⟨e,rfl⟩ := sourceHex_intersection_neighbor hzc ⟨p,hc,hz⟩
    by_cases hed : e = d
    · exact Or.inr (by rw [hed])
    rcases sourceHex_third_neighbor_at_endpoint c d e p hed hc hd hz with h | h
    · exact (hleft h).elim
    · exact (hright h).elim
  · rintro (rfl | rfl)
    · exact hc
    · exact hd

/-- A unique incident carrier contains the point in its ambient interior. -/
theorem sourceHex_singleton_incident_interior (c : ℤ × ℤ) (p : ℝ × ℝ)
    (hc : p ∈ sourceHexCarrier c)
    (hunique : ∀ z, p ∈ sourceHexCarrier z → z = c) :
    p ∈ interior (sourceHexCarrier c) := by
  have hstar : incidentStar sourceHexCarrier p = sourceHexCarrier c := by
    ext x
    change (x ∈ ⋃ i : {i // p ∈ sourceHexCarrier i}, sourceHexCarrier i.val) ↔ _
    constructor
    · rintro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rwa [hunique i.val i.property] at hi
    · intro hx
      exact mem_iUnion.mpr ⟨⟨c,hc⟩,hx⟩
  have h := mem_interior_incidentStar sourceHexCarrier sourceHex_locallyFinite
    sourceHex_isClosed sourceHex_plane_cover p
  rwa [hstar] at h

/-- Every point has exactly a one-cell, two-cell edge, or three-cell corner star.
The ordering of the triple matches directions d and d+1. -/
theorem sourceHex_incidence_classification (p : ℝ × ℝ) :
    (∃ c, p ∈ interior (sourceHexCarrier c) ∧
      ∀ z, p ∈ sourceHexCarrier z ↔ z = c) ∨
    (∃ c d, ∃ t : ℝ, t ∈ Ioo (0:ℝ) 1 ∧
      p = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t ∧
      ∀ z, p ∈ sourceHexCarrier z ↔ z = c ∨ z = sourceHexNeighbor c d) ∨
    (∃ c d, p = sourceHexCornerAt c (d+1) ∧
      ∀ z, p ∈ sourceHexCarrier z ↔
        z = c ∨ z = sourceHexNeighbor c d ∨ z = sourceHexNeighbor c (d+1)) := by
  classical
  obtain ⟨c,hc⟩ := sourceHex_plane_cover p
  by_cases hsingle : ∀ z, p ∈ sourceHexCarrier z → z = c
  · left
    refine ⟨c,sourceHex_singleton_incident_interior c p hc hsingle,?_⟩
    intro z
    exact ⟨hsingle z,fun hz => hz.symm ▸ hc⟩
  push Not at hsingle
  obtain ⟨z,hz,hzc⟩ := hsingle
  obtain ⟨d,rfl⟩ := sourceHex_intersection_neighbor hzc ⟨p,hc,hz⟩
  by_cases hleft : p = sourceHexCornerAt c d
  · right; right
    let e : Fin 6 := rotateTurn 5 d
    have he : e+1 = d := by fin_cases d <;> rfl
    have hp : p = sourceHexCornerAt c (e+1) := by rw [he]; exact hleft
    refine ⟨c,e,hp,?_⟩
    intro z
    rw [hp]
    exact sourceHexCornerAt_incident_iff c z e
  by_cases hright : p = sourceHexCornerAt c (d+1)
  · right; right
    refine ⟨c,d,hright,?_⟩
    intro z
    rw [hright]
    exact sourceHexCornerAt_incident_iff c z d
  right; left
  have hsegment : p ∈ segment ℝ (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) := by
    rw [←sourceHex_neighbor_intersection_segment]
    exact ⟨hc,hz⟩
  rw [segment_eq_image_lineMap] at hsegment
  obtain ⟨t,⟨ht0,ht1⟩,hpt⟩ := hsegment
  have ht0ne : t ≠ 0 := by
    intro ht
    apply hleft
    rw [←hpt,ht]
    simp
  have ht1ne : t ≠ 1 := by
    intro ht
    apply hright
    rw [←hpt,ht]
    simp
  exact ⟨c,d,t,⟨lt_of_le_of_ne ht0 ht0ne.symm,lt_of_le_of_ne ht1 ht1ne⟩,
    hpt.symm,fun z => sourceHex_edge_incident_iff c z d p hc hz hleft hright⟩

end
end SpectreGeometry.ReverseExistence
