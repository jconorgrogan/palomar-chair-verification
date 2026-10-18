module

public import SpectreGeometry.ReverseClusterTriangulationSource00Faces
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces
public import SpectreGeometry.ReverseClusterTriangulationCarriers
public import SpectreGeometry.ReverseClusterTriangulationFacesExistsReal
public import SpectreGeometry.ReverseClusterTriangulationInjective

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
set_option maxRecDepth 100000

theorem source0_family_has_faces : FamilyHasFaces sourceFamily0 := by
  apply familyHasFaces_of_row_exists sourceFamily0
  intro i
  have hi : i.val < 208 := by simpa only [source0Family_length] using i.isLt
  exact source0AllFaceRows ⟨i.val,hi⟩

theorem source1_family_has_faces : FamilyHasFaces sourceFamily1 := by
  apply familyHasFaces_of_row_exists sourceFamily1
  intro i
  have hi : i.val < 218 := by simpa only [source1Family_length] using i.isLt
  exact source1AllFaceRows ⟨i.val,hi⟩

theorem source2_family_has_faces : FamilyHasFaces sourceFamily2 := by
  apply familyHasFaces_of_row_exists sourceFamily2
  intro i
  have hi : i.val < 218 := by simpa only [source2Family_length] using i.isLt
  exact source2AllFaceRows ⟨i.val,hi⟩

theorem source3_family_has_faces : FamilyHasFaces sourceFamily3 := by
  apply familyHasFaces_of_row_exists sourceFamily3
  intro i
  have hi : i.val < 218 := by simpa only [source3Family_length] using i.isLt
  exact source3AllFaceRows ⟨i.val,hi⟩

theorem source4_family_has_faces : FamilyHasFaces sourceFamily4 := by
  apply familyHasFaces_of_row_exists sourceFamily4
  intro i
  have hi : i.val < 218 := by simpa only [source4Family_length] using i.isLt
  exact source4AllFaceRows ⟨i.val,hi⟩

theorem source5_family_has_faces : FamilyHasFaces sourceFamily5 := by
  apply familyHasFaces_of_row_exists sourceFamily5
  intro i
  have hi : i.val < 218 := by simpa only [source5Family_length] using i.isLt
  exact source5AllFaceRows ⟨i.val,hi⟩

theorem source6_family_has_faces : FamilyHasFaces sourceFamily6 := by
  apply familyHasFaces_of_row_exists sourceFamily6
  intro i
  have hi : i.val < 218 := by simpa only [source6Family_length] using i.isLt
  exact source6AllFaceRows ⟨i.val,hi⟩

theorem source7_family_has_faces : FamilyHasFaces sourceFamily7 := by
  apply familyHasFaces_of_row_exists sourceFamily7
  intro i
  have hi : i.val < 218 := by simpa only [source7Family_length] using i.isLt
  exact source7AllFaceRows ⟨i.val,hi⟩

theorem source8_family_has_faces : FamilyHasFaces sourceFamily8 := by
  apply familyHasFaces_of_row_exists sourceFamily8
  intro i
  have hi : i.val < 218 := by simpa only [source8Family_length] using i.isLt
  exact source8AllFaceRows ⟨i.val,hi⟩

theorem target0_family_has_faces : FamilyHasFaces targetMeshFamily0 := by
  apply familyHasFaces_of_row_exists targetMeshFamily0
  intro i
  have hi : i.val < 208 := by simpa only [target0Family_length] using i.isLt
  exact target0AllFaceRows ⟨i.val,hi⟩

theorem target1_family_has_faces : FamilyHasFaces targetMeshFamily1 := by
  apply familyHasFaces_of_row_exists targetMeshFamily1
  intro i
  have hi : i.val < 218 := by simpa only [target1Family_length] using i.isLt
  exact target1AllFaceRows ⟨i.val,hi⟩

theorem all_source_families_have_faces : ∀ k : Fin 9, FamilyHasFaces (sourceFamily k) := by
  exact Fin.cases (source0_family_has_faces) (Fin.cases (source1_family_has_faces) (Fin.cases (source2_family_has_faces) (Fin.cases (source3_family_has_faces) (Fin.cases (source4_family_has_faces) (Fin.cases (source5_family_has_faces) (Fin.cases (source6_family_has_faces) (Fin.cases (source7_family_has_faces) (Fin.cases (source8_family_has_faces) (fun i => Fin.elim0 i)))))))))
theorem all_target_families_have_faces : ∀ k : Fin 9, FamilyHasFaces (targetFamily k) := by
  exact Fin.cases (target0_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (Fin.cases (target1_family_has_faces) (fun i => Fin.elim0 i)))))))))

end
end SpectreGeometry.ReverseClusterTriangulation
