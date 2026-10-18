module

public import SpectreGeometry.ReverseRawInverseChartData
public import SpectreGeometry.ReversePhysicalClusterReal
public import SpectreGeometry.DevelopedLiteralBody

@[expose] public section


/-! The common raw-frame reflection is explicit. After this frame change, each
literal raw tile's vertices are exactly the certified forward chart's targets. -/
namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open SpectreClusters Deformation

def rawFrame : RealPoint →ₗ[ℝ] RealPoint := gridEmbeddingLinear.comp gridReflectionLinear

theorem quarterPoint_rawFrame4 (p : SpectreClusters.Point) :
    quarterPoint (rawFrame4 p) = rawFrame (integerPoint p) := by
  ext <;> simp only [quarterPoint,rawFrame4,ExactPoint.eval,Quad3.eval,
    rawFrame,LinearMap.comp_apply,gridEmbeddingLinear,gridReflectionLinear,
    LinearMap.coe_mk,AddHom.coe_mk,integerPoint,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,Int.cast_sub,Int.cast_neg,Int.cast_mul,Int.cast_ofNat] <;> ring

theorem quarterPoint_targetVertex4 (k : Fin 12) (e : Fin 14) :
    quarterPoint (targetVertex4 k e) = realDeformedVertex k e := by
  rw [quarterPoint,targetVertex4_eval,smul_smul]
  norm_num

def rawTileTargetOrigin (p : HTPlacement) : RealPoint :=
  rawFrame (integerPoint (lattice p.center))+quarterPoint (rawTargetOffset4 p.kind p.turn)

/-- Source-correct alignment with the already checked 144 affine charts. -/
theorem raw_placed_vertex_target (p : HTPlacement) (e : Fin 14) :
    rawFrame (integerPoint (rawPlacedVertex p (physicalIndex p.kind e))) =
      rawTileTargetOrigin p+realDeformedVertex (physicalTurn p) e := by
  have h := congrArg quarterPoint (raw_local_target_binding p.kind p.turn e)
  rw [quarterPoint_add,quarterPoint_targetVertex4] at h
  change quarterPoint (rawFrame4 _) = _ at h
  rw [quarterPoint_rawFrame4] at h
  rw [rawPlacedVertex,integerPoint_add,map_add,h]
  simp only [rawTileTargetOrigin,physicalTurn,_root_.add_assoc]

end
end SpectreGeometry.ReversePhysicalCluster
