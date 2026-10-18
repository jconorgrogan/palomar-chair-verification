module

public import SpectreGeometry.DeformedVertexData
public import SpectreClusters.LiteralData

@[expose] public section


/-! Exact vertex binding between the physical team's parity development
and the Spectre H/T literals. One global reflection is explicit. These
are vertex-coordinate and vertex-set equalities, not real-body equalities
or a homeomorphism of the developed plane. -/
namespace SpectreClusters.DeformedLiteralBinding

def reflectPoint (p : Point) : Point := (p.1, -p.1-p.2)

def reflectCenter (p : Point) : Point := (p.1+p.2, -p.2)

theorem reflectPoint_involutive (p : Point) : reflectPoint (reflectPoint p) = p := by
  apply Prod.ext <;> simp [reflectPoint] <;> omega

theorem reflectPoint_add (p q : Point) :
    reflectPoint (add p q) = add (reflectPoint p) (reflectPoint q) := by
  apply Prod.ext <;> simp [reflectPoint,add] <;> omega

theorem reflectPoint_lattice (p : Point) :
    reflectPoint (lattice p) = lattice (reflectCenter p) := by
  apply Prod.ext <;> simp [reflectPoint,lattice,reflectCenter] <;> omega

theorem reflected_center_lattice (p : Point)
    (hp : SpectreGeometry.InKiteCenterLattice p) :
    SpectreGeometry.InKiteCenterLattice (reflectPoint p) := by
  simp only [SpectreGeometry.InKiteCenterLattice,reflectPoint] at *
  omega

theorem reflected_center_lattice_iff (p : Point) :
    SpectreGeometry.InKiteCenterLattice (reflectPoint p) ↔
      SpectreGeometry.InKiteCenterLattice p := by
  constructor
  · intro hp
    simpa only [reflectPoint_involutive] using reflected_center_lattice (reflectPoint p) hp
  · exact reflected_center_lattice p

def literalKind (k : Fin 12) : HTKind :=
  if k.val % 2 = 0 then .turtle else .hat

def literalTurn (k : Fin 12) : Turn :=
  ⟨(6-k.val/2)%6, Nat.mod_lt _ (by decide)⟩

def literalIndex (k : Fin 12) (i : Fin 14) : Fin 14 :=
  ⟨((if k.val % 2 = 0 then 15 else 27)-i.val)%14, Nat.mod_lt _ (by decide)⟩

def literalVertex (kind : HTKind) (i : Fin 14) : Point :=
  (htRefinedPolygon kind).getD i.val (0,0)

def literalPlacedVertex (k : Fin 12) (i : Fin 14) : Point :=
  add (reflectPoint (SpectreGeometry.deformedOffset k))
    (rotate (literalTurn k) (literalVertex (literalKind k) i))

theorem literalIndex_involutive : ∀ (k : Fin 12) (i : Fin 14),
    literalIndex k (literalIndex k i) = i := by decide

theorem refinedPolygon_indexed (kind : HTKind) :
    (List.finRange 14).map (literalVertex kind) = htRefinedPolygon kind := by
  cases kind <;> rfl

set_option maxRecDepth 100000 in
/-- All twelve global physical orientations use the same reflection.
Even orientations give turtles, odd orientations hats. -/
theorem developed_vertex_literal : ∀ (k : Fin 12) (i : Fin 14),
    reflectPoint (SpectreGeometry.deformedVertex k i) =
      literalPlacedVertex k (literalIndex k i) := by decide

theorem developed_vertex_set (k : Fin 12) (p : Point) :
    p ∈ (List.finRange 14).map (fun i => reflectPoint (SpectreGeometry.deformedVertex k i)) ↔
    p ∈ (List.finRange 14).map (literalPlacedVertex k) := by
  constructor
  · intro hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨literalIndex k i, List.mem_finRange _,
      (developed_vertex_literal k i).symm⟩
  · intro hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    refine List.mem_map.mpr ⟨literalIndex k i, List.mem_finRange _, ?_⟩
    rw [developed_vertex_literal,literalIndex_involutive]

theorem developed_vertex_set_literal_polygon (k : Fin 12) (p : Point) :
    p ∈ (List.finRange 14).map (fun i => reflectPoint (SpectreGeometry.deformedVertex k i)) ↔
    p ∈ (htRefinedPolygon (literalKind k)).map
      (fun q => add (reflectPoint (SpectreGeometry.deformedOffset k))
        (rotate (literalTurn k) q)) := by
  rw [developed_vertex_set,←refinedPolygon_indexed]
  simp only [List.map_map]
  rfl

end SpectreClusters.DeformedLiteralBinding
