module

public import SpectreFinite.RadiusFiveSourceRows
public import SpectreFinite.RadiusThreeRowProjection

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem sourceRowsCanonical0_0 : RadiusFourPruning.final0_0 =
    sourceRows0_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_0
theorem sourceRowsCanonical0_1 : RadiusFourPruning.final0_1 =
    sourceRows0_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_1
theorem sourceRowsCanonical0_2 : RadiusFourPruning.final0_2 =
    sourceRows0_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_2
theorem sourceRowsCanonical0_3 : RadiusFourPruning.final0_3 =
    sourceRows0_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_3
theorem sourceRowsCanonical0_4 : RadiusFourPruning.final0_4 =
    sourceRows0_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_4
theorem sourceRowsCanonical0_5 : RadiusFourPruning.final0_5 =
    sourceRows0_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows0_5
theorem sourceRowsCanonical1_0 : RadiusFourPruning.final1_0 =
    sourceRows1_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_0
theorem sourceRowsCanonical1_1 : RadiusFourPruning.final1_1 =
    sourceRows1_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_1
theorem sourceRowsCanonical1_2 : RadiusFourPruning.final1_2 =
    sourceRows1_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_2
theorem sourceRowsCanonical1_3 : RadiusFourPruning.final1_3 =
    sourceRows1_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_3
theorem sourceRowsCanonical1_4 : RadiusFourPruning.final1_4 =
    sourceRows1_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_4
theorem sourceRowsCanonical1_5 : RadiusFourPruning.final1_5 =
    sourceRows1_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows1_5
theorem sourceRowsCanonical2_0 : RadiusFourPruning.final2_0 =
    sourceRows2_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_0
theorem sourceRowsCanonical2_1 : RadiusFourPruning.final2_1 =
    sourceRows2_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_1
theorem sourceRowsCanonical2_2 : RadiusFourPruning.final2_2 =
    sourceRows2_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_2
theorem sourceRowsCanonical2_3 : RadiusFourPruning.final2_3 =
    sourceRows2_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_3
theorem sourceRowsCanonical2_4 : RadiusFourPruning.final2_4 =
    sourceRows2_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_4
theorem sourceRowsCanonical2_5 : RadiusFourPruning.final2_5 =
    sourceRows2_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows2_5
theorem sourceRowsCanonical3_0 : RadiusFourPruning.final3_0 =
    sourceRows3_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_0
theorem sourceRowsCanonical3_1 : RadiusFourPruning.final3_1 =
    sourceRows3_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_1
theorem sourceRowsCanonical3_2 : RadiusFourPruning.final3_2 =
    sourceRows3_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_2
theorem sourceRowsCanonical3_3 : RadiusFourPruning.final3_3 =
    sourceRows3_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_3
theorem sourceRowsCanonical3_4 : RadiusFourPruning.final3_4 =
    sourceRows3_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_4
theorem sourceRowsCanonical3_5 : RadiusFourPruning.final3_5 =
    sourceRows3_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows3_5
theorem sourceRowsCanonical4_0 : RadiusFourPruning.final4_0 =
    sourceRows4_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_0
theorem sourceRowsCanonical4_1 : RadiusFourPruning.final4_1 =
    sourceRows4_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_1
theorem sourceRowsCanonical4_2 : RadiusFourPruning.final4_2 =
    sourceRows4_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_2
theorem sourceRowsCanonical4_3 : RadiusFourPruning.final4_3 =
    sourceRows4_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_3
theorem sourceRowsCanonical4_4 : RadiusFourPruning.final4_4 =
    sourceRows4_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_4
theorem sourceRowsCanonical4_5 : RadiusFourPruning.final4_5 =
    sourceRows4_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows4_5
theorem sourceRowsCanonical5_0 : RadiusFourPruning.final5_0 =
    sourceRows5_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_0
theorem sourceRowsCanonical5_1 : RadiusFourPruning.final5_1 =
    sourceRows5_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_1
theorem sourceRowsCanonical5_2 : RadiusFourPruning.final5_2 =
    sourceRows5_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_2
theorem sourceRowsCanonical5_3 : RadiusFourPruning.final5_3 =
    sourceRows5_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_3
theorem sourceRowsCanonical5_4 : RadiusFourPruning.final5_4 =
    sourceRows5_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_4
theorem sourceRowsCanonical5_5 : RadiusFourPruning.final5_5 =
    sourceRows5_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows5_5
theorem sourceRowsCanonical6_0 : RadiusFourPruning.final6_0 =
    sourceRows6_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_0
theorem sourceRowsCanonical6_1 : RadiusFourPruning.final6_1 =
    sourceRows6_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_1
theorem sourceRowsCanonical6_2 : RadiusFourPruning.final6_2 =
    sourceRows6_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_2
theorem sourceRowsCanonical6_3 : RadiusFourPruning.final6_3 =
    sourceRows6_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_3
theorem sourceRowsCanonical6_4 : RadiusFourPruning.final6_4 =
    sourceRows6_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_4
theorem sourceRowsCanonical6_5 : RadiusFourPruning.final6_5 =
    sourceRows6_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows6_5
theorem sourceRowsCanonical7_0 : RadiusFourPruning.final7_0 =
    sourceRows7_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_0
theorem sourceRowsCanonical7_1 : RadiusFourPruning.final7_1 =
    sourceRows7_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_1
theorem sourceRowsCanonical7_2 : RadiusFourPruning.final7_2 =
    sourceRows7_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_2
theorem sourceRowsCanonical7_3 : RadiusFourPruning.final7_3 =
    sourceRows7_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_3
theorem sourceRowsCanonical7_4 : RadiusFourPruning.final7_4 =
    sourceRows7_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_4
theorem sourceRowsCanonical7_5 : RadiusFourPruning.final7_5 =
    sourceRows7_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows7_5
theorem sourceRowsCanonical8_0 : RadiusFourPruning.final8_0 =
    sourceRows8_0.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_0
theorem sourceRowsCanonical8_1 : RadiusFourPruning.final8_1 =
    sourceRows8_1.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_1
theorem sourceRowsCanonical8_2 : RadiusFourPruning.final8_2 =
    sourceRows8_2.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_2
theorem sourceRowsCanonical8_3 : RadiusFourPruning.final8_3 =
    sourceRows8_3.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_3
theorem sourceRowsCanonical8_4 : RadiusFourPruning.final8_4 =
    sourceRows8_4.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_4
theorem sourceRowsCanonical8_5 : RadiusFourPruning.final8_5 =
    sourceRows8_5.map (fun row => (hexRegion 4).zip row) := RadiusFourPruning.final_eq_stateRows8_5
end SpectreFinite.HexSearch.RadiusFive
