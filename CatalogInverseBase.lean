module
public import ContactInverseReuse
public import SparseMonotiles.CarrierHierarchyExactStages
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
open Contact CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def catalogRow (i : Fin 408) : Pose 7 :=
  Catalog7.supplied.get ⟨i.val, by simpa only [Catalog7.supplied_count] using i.isLt⟩

/-- Untrusted proposed index witnesses, checked against every full signed pose below. -/
def inverseIndexTable : List (Fin 408) := [
  3, 25, 402, 0, 28, 159, 158, 161, 160, 163, 162, 166, 165, 167, 182, 181, 184, 254, 252, 253, 256, 257, 259, 275,
  382, 1, 384, 399, 4, 406, 407, 130, 129, 133, 132, 136, 135, 150, 149, 151, 153, 280, 278, 279, 282, 49, 52, 364,
  372, 45, 54, 370, 46, 366, 50, 374, 375, 125, 124, 284, 300, 301, 101, 100, 105, 104, 121, 120, 306, 304, 305, 309,
  94, 93, 324, 81, 342, 78, 77, 84, 345, 75, 339, 343, 79, 348, 349, 96, 95, 308, 102, 122, 328, 73, 72, 88,
  87, 332, 330, 331, 63, 62, 90, 352, 65, 64, 336, 355, 311, 113, 112, 316, 110, 109, 314, 116, 115, 318, 319, 320,
  67, 66, 91, 333, 58, 57, 358, 356, 357, 32, 31, 377, 34, 33, 378, 36, 35, 138, 137, 287, 289, 288, 143, 142,
  145, 144, 291, 292, 293, 38, 37, 39, 359, 40, 379, 388, 386, 387, 6, 5, 8, 7, 10, 9, 389, 12, 11, 13,
  390, 171, 173, 169, 174, 170, 172, 261, 262, 263, 260, 264, 265, 15, 14, 391, 16, 392, 187, 186, 189, 188, 191, 190,
  193, 192, 195, 194, 197, 196, 199, 198, 201, 200, 203, 202, 205, 204, 207, 206, 209, 208, 211, 210, 213, 212, 214, 216,
  215, 217, 243, 242, 250, 251, 225, 224, 223, 222, 227, 226, 229, 228, 231, 230, 233, 232, 235, 234, 237, 236, 239, 238,
  248, 249, 219, 218, 246, 247, 244, 245, 240, 241, 220, 221, 18, 19, 17, 393, 20, 21, 394, 22, 178, 175, 176, 177,
  179, 180, 268, 272, 266, 271, 270, 269, 267, 395, 396, 23, 397, 398, 42, 43, 41, 360, 44, 380, 59, 361, 362, 139,
  141, 140, 290, 146, 147, 148, 295, 294, 299, 298, 297, 296, 60, 61, 381, 363, 69, 70, 68, 334, 89, 71, 353, 108,
  313, 312, 114, 317, 111, 315, 117, 118, 119, 323, 322, 321, 74, 335, 337, 354, 92, 338, 98, 99, 97, 123, 307, 325,
  106, 326, 329, 82, 346, 347, 76, 83, 344, 80, 340, 341, 85, 86, 351, 350, 103, 310, 327, 107, 127, 128, 126, 152,
  281, 285, 286, 303, 47, 367, 53, 365, 373, 371, 51, 369, 48, 368, 55, 56, 376, 131, 134, 154, 283, 302, 24, 400,
  26, 405, 156, 157, 155, 164, 168, 183, 185, 255, 258, 273, 274, 276, 277, 27, 383, 404, 2, 403, 401, 385, 29, 30
]
def inverseIndex (i : Fin 408) : Fin 408 := inverseIndexTable.getD i.val 0

/-- All output permutation coordinates, signs, and translations are checked. -/
def CatalogInverseRow (i : Fin 408) : Prop :=
  ∀ j : Fin 7,
    (inversePose (catalogRow i)).perm j = (catalogRow (inverseIndex i)).perm j ∧
    (inversePose (catalogRow i)).negative j = (catalogRow (inverseIndex i)).negative j ∧
    (inversePose (catalogRow i)).shift j = (catalogRow (inverseIndex i)).shift j

instance (i : Fin 408) : Decidable (CatalogInverseRow i) := by
  unfold CatalogInverseRow
  infer_instance

end SparseMonotiles.ContactInverseReuse
