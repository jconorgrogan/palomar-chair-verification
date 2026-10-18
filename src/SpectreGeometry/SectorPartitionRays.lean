module

public import SpectreGeometry.PhysicalVertexEdgeStar
public import SpectreGeometry.SectorBoundaryRays

@[expose] public section


namespace SpectreGeometry
noncomputable section

theorem sector_partition_edge_rays {ι : Type*}
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpart : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    (root : ι) (e : Fin 14) (hkroot : k root = 0) (hbroot : b root = .inr e)
    (hcorners : ∀ a, a ≠ root → ∃ q, b a = .inl q) :
    (∃ a q, a ≠ root ∧ b a = .inl q ∧
      directionAdd (k a) (edgeTurn q) = directionAdd (edgeTurn e) 6) ∧
    (∃ a q, a ≠ root ∧ b a = .inl q ∧
      directionAdd (k a) (edgeTurn (previous q)) = directionAdd (edgeTurn e) 6) := by
  have hr : ∀ d, slotSector (b root) (directionAdd (directionInverse (k root)) d) ↔ edgeSector e d := by
    intro d
    rw [hkroot,hbroot]
    change edgeSector e (directionAdd 0 d) ↔ edgeSector e d
    rw [direction_zero_add]
  have huniq : ∀ a d, a ≠ root → edgeSector e d →
      ¬slotSector (b a) (directionAdd (directionInverse (k a)) d) := by
    intro a d ha hd hm
    obtain ⟨v,hv,hu⟩ := hpart d
    exact ha ((hu a hm).trans (hu root ((hr d).2 hd)).symm)
  have hbs := edge_sector_boundary_samples e
  constructor
  · obtain ⟨a,ha,_⟩ := hpart (directionAdd (edgeTurn e) 6)
    have har : a ≠ root := by
      intro he
      subst a
      exact hbs.2.2.1 ((hr _).1 ha)
    obtain ⟨q,hq⟩ := hcorners a har
    have hn := huniq a (directionAdd (edgeTurn e) 5) har hbs.1
    have he : directionAdd (directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 6)) 11 =
        directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 5) := by
      rw [direction_add_assoc,direction_add_assoc]
      rfl
    have ht := slot_sector_initial_ray (b a) (directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 6)) ha (by rwa [he])
    rw [hq] at ht
    change directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 6) = edgeTurn q at ht
    refine ⟨a,q,har,hq,?_⟩
    rw [←ht,←direction_add_assoc,direction_inverse_right,direction_zero_add]
  · obtain ⟨a,ha,_⟩ := hpart (directionAdd (edgeTurn e) 11)
    have har : a ≠ root := by
      intro he
      subst a
      exact hbs.2.2.2 ((hr _).1 ha)
    obtain ⟨q,hq⟩ := hcorners a har
    have hn := huniq a (edgeTurn e) har hbs.2.1
    have he : directionAdd (directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 11)) 1 =
        directionAdd (directionInverse (k a)) (edgeTurn e) := by
      rw [direction_add_assoc,direction_add_assoc]
      change directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 0) = _
      rw [direction_add_zero]
    have ht := slot_sector_final_ray (b a) (directionAdd (directionInverse (k a)) (directionAdd (edgeTurn e) 11)) ha (by rwa [he])
    rw [he,hq] at ht
    change directionAdd (directionInverse (k a)) (edgeTurn e) = directionAdd (edgeTurn (previous q)) 6 at ht
    have hh := congrArg (fun d => directionAdd (k a) d) ht
    rw [←direction_add_assoc,direction_inverse_right,direction_zero_add] at hh
    have hh' := congrArg (fun d => directionAdd d 6) hh
    rw [direction_add_assoc,direction_add_assoc] at hh'
    change directionAdd (edgeTurn e) 6 = directionAdd (k a) (directionAdd (edgeTurn (previous q)) 0) at hh'
    rw [direction_add_zero] at hh'
    exact ⟨a,q,har,hq,hh'.symm⟩

end
end SpectreGeometry
