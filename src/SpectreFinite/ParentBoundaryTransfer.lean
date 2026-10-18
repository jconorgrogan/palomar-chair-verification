module

public import SpectreFinite.ParentBoundaryGeometry

@[expose] public section


/-! Sound table and occurrence transfers for the exact native boundary tests. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

theorem incidentOwners_congr (own own' : Position → List Position) (v : Vertex)
    (h : ∀ x ∈ incidentCells v, own x = own' x) :
    incidentOwners own v = incidentOwners own' v := by
  unfold incidentOwners List.flatMap
  congr 2
  exact List.map_congr_left h

theorem structure_local (own own' : Position → List Position) (k : TileKind)
    (ns : List Position) (he : ∀ x ∈ support k, own x = own' x)
    (h : Structure own k ns) : Structure own' k ns := by
  obtain ⟨hn,hd,hz,hs,hv,hc,ht⟩ := h
  obtain ⟨qs,qv,qc,qt⟩ := query_support k
  refine ⟨hn,hd,hz,?_,?_,?_,?_⟩
  · intro s e hm
    rw [← he _ (qs s e hm)]
    exact hs s e hm
  · intro s
    rw [← incidentOwners_congr own own' (vertexAt k s) (fun x hx => he x (qv s x hx))]
    exact hv s
  · intro e hm
    rw [← incidentOwners_congr own own' (start (children k) e)
      (fun x hx => he x (qc e hm x hx))]
    exact hc e hm
  · intro i
    rw [← he _ (qt i).1, ← he _ (qt i).2]
    exact ht i

/-- The finite table is only a witness. Every listed value is checked against
owners, and this theorem uses the successful lookup rather than a default. -/
theorem tableOwners_sound (f : Position → State) (table : OwnerTable)
    (h : TableSound f table) (x : Position) (hx : tableOwners table x ≠ []) :
    tableOwners table x = owners f x := by
  unfold tableOwners at hx ⊢
  cases he : table.find? (fun a => a.1 == x) with
  | none => simp [he] at hx
  | some a =>
    have hm := List.mem_of_find?_eq_some he
    have ha : a.1 = x := by simpa using List.find?_some he
    simpa [he,ha] using (h a hm).symm

theorem structure_of_table (f : Position → State) (table : OwnerTable)
    (k : TileKind) (ns : List Position) (h : TableSound f table)
    (hc : ∀ x ∈ support k, tableOwners table x ≠ [])
    (hb : Structure (tableOwners table) k ns) : Structure (owners f) k ns :=
  structure_local _ _ k ns (fun x hx => tableOwners_sound f table h x (hc x hx)) hb

/-- Transfer from the efficient encoding uses the proved radius-three support;
no default cell outside the actual radius-five domain contributes. -/
theorem encodedPatch_rootStructure (row : List State)
    (h : RootStructure (indexedField row)) : RootStructure (patchState (encodedPatch row)) := by
  obtain ⟨k,ns,hp,hb⟩ := h
  refine ⟨k,ns,?_,?_⟩
  · rw [encodedPatch_rootParent]
    exact hp
  · exact structure_local _ _ k ns (fun x hx =>
      (encodedPatch_owners row x (support_radiusThree k x hx)).symm) hb

theorem rootStructure_extract (f : Position → State) (center : Position)
    (h : RootStructure (patchState (extract f center (hexRegion 5)))) :
    RootStructure (shiftedField f center) := by
  obtain ⟨k,ns,hp,hb⟩ := h
  refine ⟨k,ns,?_,?_⟩
  · rw [rootParent_extract] at hp
    exact hp
  · exact structure_local _ _ k ns (fun x hx =>
      owners_extract f center (hexRegion 5) x
        (radiusThree_candidates_covered x (support_radiusThree k x hx))) hb

/-- The only passage from a finite family to arbitrary occurrences is explicit.
This theorem does not assert the needed occurrence-completeness hypothesis. -/
theorem rootStructure_of_radiusFive_certificate (family : List Patch)
    (hc : ∀ p ∈ family, patchState p (0,0) = (0,0) → RootStructure (patchState p))
    (f : Position → State) (hocc : OccurrenceComplete f (hexRegion 5) family)
    (center : Position) (hg : f center = (0,0)) : RootStructure (shiftedField f center) := by
  apply rootStructure_extract
  apply hc _ (hocc center)
  change patchState (restriction (shiftedField f center) (hexRegion 5)) (0,0) = (0,0)
  rw [patchState_restriction _ _ _ (by decide)]
  simpa [shiftedField,addPos] using hg

/-- Precisely the root and the two neighboring parents adjacent in the cyclic
six-side order meet the author marker. Incident ranges over every axial cell. -/
theorem marker_parent_membership (f : Position → State) (k : TileKind)
    (ns : List Position) (h : Structure (owners f) k ns) (s : Fin 6) (a : Position) :
    (∃ x, Incident x (vertexAt k s) ∧ a ∈ owners f x) ↔
      a = (0,0) ∨ a = ns.getD (previous s) (0,0) ∨ a = ns.getD s.val (0,0) := by
  rw [← mem_incidentOwners_iff]
  have hp := h.2.2.2.2.1 s
  rw [hp.mem_iff]
  simp

/-- Three distinct parent anchors occur, since incidentOwners removes duplicates. -/
theorem marker_parent_count (f : Position → State) (k : TileKind)
    (ns : List Position) (h : Structure (owners f) k ns) (s : Fin 6) :
    (incidentOwners (owners f) (vertexAt k s)).length = 3 := by
  have hp := (h.2.2.2.2.1 s).length_eq
  simpa using hp

#print axioms structure_of_table
#print axioms encodedPatch_rootStructure
#print axioms rootStructure_of_radiusFive_certificate
#print axioms marker_parent_membership
#print axioms marker_parent_count
end SpectreFinite.HexSearch.ParentBoundary
