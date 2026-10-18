module

public import SpectreGeometry.ReversePhysicalClusterChartFacesData

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
open SpectreClusters SpectreClusters.ReverseExistence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def physicalBoundaryChartOwnerTable : List (List (List Nat)) := [[[47,44,43,55,54,54,51],[51,50,79,78,78,75,75],[74,74,72,63,62,91,90,90,87,87],[86,86,84,84,18,18,15,15,14,31],[30,30,27,27,26],[26,24,36,37,47]],[[47,44,43,55,54,54,51,51,50,79],[78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99],[98,98,96,15,14,31,30,30,27,27],[26,26,24,36,37,47]],[[47,44,43,55,54,54,51,51,50,79],[78,78,75,75,74],[74,72,63,62,91,90,90,87,87,86,103],[102,102,99,99,98],[98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]],[[47,44,43,55,54,54,51,51,50,79],[78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99],[98,98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]],[[47,44,43,55,54,54,51],[51,50,79,78,78,75,75,74],[74,72,63,62,91,90,90,87,87,86,103],[102,102,99,99,98],[98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]],[[47,44,43,55,54,54,51],[51,50,79,78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99],[98,98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]],[[54,54,51,51,50,79],[78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99],[98,98,96,15,14,31,30,30,27,27],[26,26,24,36,37,47,47,44,43,55]],[[47,44,43,55,54,54,51,51,50,79],[78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99,98],[98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]],[[47,44,43,55,54,54,51],[51,50,79,78,78,75,75,74],[74,72,63,62,91,90,90,87],[87,86,103,102,102,99,99,98],[98,96,15,14,31,30,30,27,27,26],[26,24,36,37,47]]]

def physicalBoundaryChartOwner (k : Fin 9) (d : Fin 6) (j : Nat) : Nat :=
  (((physicalBoundaryChartOwnerTable.getD k.val []).getD d.val []).getD j 999)

def PhysicalBoundaryChartOwnerCertificate (k : Fin 9) (d : Fin 6) : Prop :=
  ∀ j ∈ List.range (((markedPaths k).getD d.val []).length - 1),
    let z := physicalBoundaryChartOwner k d j
    z < (chartFamily (k.val != 0)).length ∧
      ((markedPaths k).getD d.val []).getD j (0,0) ∈
        ((chartFamily (k.val != 0)).getD z default).vertices ∧
      ((markedPaths k).getD d.val []).getD (j+1) (0,0) ∈
        ((chartFamily (k.val != 0)).getD z default).vertices

end SpectreGeometry.ReversePhysicalClusterCharts
