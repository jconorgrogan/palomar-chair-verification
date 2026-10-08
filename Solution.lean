module

public import HENRY.Transport
public import T7ExactStrongMonotile

@[expose] public section
namespace PalomarMonotiles

/- UNCOMPILED TEMPLATE: the final internal theorem must first be proved and
individually kernel checked from the completed exact contact classification.
This file deliberately imports neither Challenge nor its theorem hole. -/
theorem T7_strongAperiodicity : T7StrongClaim :=
  HENRY.Binding.strongClaim_of_internal SparseMonotiles.ExactCompactT7Strong.final_bound

end PalomarMonotiles
