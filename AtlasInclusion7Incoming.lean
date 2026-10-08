module
public import AtlasInclusion7Base
@[expose] public section
namespace CompactT7Preparation
open RegisteredPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem pose2_generated : GeneratedContact P7 pose2 := by
  have hA : Proper pose2.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose2 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose2.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose2.frame.negative) i.val = (pose2.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose2.frame.negative i then (4 : Int) else 0) = pose2.anchor i + 1) i

theorem pose3_generated : GeneratedContact P7 pose3 := by
  have hA : Proper pose3.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose3 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose3.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose3.frame.negative) i.val = (pose3.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose3.frame.negative i then (4 : Int) else 0) = pose3.anchor i + 1) i

theorem pose16_generated : GeneratedContact P7 pose16 := by
  have hA : Proper pose16.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose16 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose16.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose16.frame.negative) i.val = (pose16.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose16.frame.negative i then (4 : Int) else 0) = pose16.anchor i + 1) i

theorem pose19_generated : GeneratedContact P7 pose19 := by
  have hA : Proper pose19.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose19 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose19.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose19.frame.negative) i.val = (pose19.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose19.frame.negative i then (4 : Int) else 0) = pose19.anchor i + 1) i

theorem pose20_generated : GeneratedContact P7 pose20 := by
  have hA : Proper pose20.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose20 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose20.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose20.frame.negative) i.val = (pose20.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose20.frame.negative i then (4 : Int) else 0) = pose20.anchor i + 1) i

theorem pose21_generated : GeneratedContact P7 pose21 := by
  have hA : Proper pose21.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose21 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose21.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose21.frame.negative) i.val = (pose21.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose21.frame.negative i then (4 : Int) else 0) = pose21.anchor i + 1) i

theorem pose22_generated : GeneratedContact P7 pose22 := by
  have hA : Proper pose22.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose22 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose22.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose22.frame.negative) i.val = (pose22.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose22.frame.negative i then (4 : Int) else 0) = pose22.anchor i + 1) i

theorem pose25_generated : GeneratedContact P7 pose25 := by
  have hA : Proper pose25.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose25 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose25.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose25.frame.negative) i.val = (pose25.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose25.frame.negative i then (4 : Int) else 0) = pose25.anchor i + 1) i

theorem pose28_generated : GeneratedContact P7 pose28 := by
  have hA : Proper pose28.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose28 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose28.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose28.frame.negative) i.val = (pose28.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose28.frame.negative i then (4 : Int) else 0) = pose28.anchor i + 1) i

theorem pose40_generated : GeneratedContact P7 pose40 := by
  have hA : Proper pose40.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose40 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose40.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose40.frame.negative) i.val = (pose40.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose40.frame.negative i then (4 : Int) else 0) = pose40.anchor i + 1) i

theorem pose43_generated : GeneratedContact P7 pose43 := by
  have hA : Proper pose43.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose43 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose43.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose43.frame.negative) i.val = (pose43.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose43.frame.negative i then (4 : Int) else 0) = pose43.anchor i + 1) i

theorem pose44_generated : GeneratedContact P7 pose44 := by
  have hA : Proper pose44.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose44 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose44.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose44.frame.negative) i.val = (pose44.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose44.frame.negative i then (4 : Int) else 0) = pose44.anchor i + 1) i

theorem pose45_generated : GeneratedContact P7 pose45 := by
  have hA : Proper pose45.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose45 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose45.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose45.frame.negative) i.val = (pose45.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose45.frame.negative i then (4 : Int) else 0) = pose45.anchor i + 1) i

theorem pose51_generated : GeneratedContact P7 pose51 := by
  have hA : Proper pose51.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose51 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose51.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose51.frame.negative) i.val = (pose51.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose51.frame.negative i then (4 : Int) else 0) = pose51.anchor i + 1) i

theorem pose52_generated : GeneratedContact P7 pose52 := by
  have hA : Proper pose52.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose52 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose52.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose52.frame.negative) i.val = (pose52.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose52.frame.negative i then (4 : Int) else 0) = pose52.anchor i + 1) i

theorem pose54_generated : GeneratedContact P7 pose54 := by
  have hA : Proper pose54.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose54 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose54.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose54.frame.negative) i.val = (pose54.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose54.frame.negative i then (4 : Int) else 0) = pose54.anchor i + 1) i

theorem pose60_generated : GeneratedContact P7 pose60 := by
  have hA : Proper pose60.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose60 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose60.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose60.frame.negative) i.val = (pose60.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose60.frame.negative i then (4 : Int) else 0) = pose60.anchor i + 1) i

theorem pose61_generated : GeneratedContact P7 pose61 := by
  have hA : Proper pose61.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose61 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose61.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose61.frame.negative) i.val = (pose61.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose61.frame.negative i then (4 : Int) else 0) = pose61.anchor i + 1) i

theorem pose70_generated : GeneratedContact P7 pose70 := by
  have hA : Proper pose70.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose70 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose70.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose70.frame.negative) i.val = (pose70.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose70.frame.negative i then (4 : Int) else 0) = pose70.anchor i + 1) i

theorem pose74_generated : GeneratedContact P7 pose74 := by
  have hA : Proper pose74.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose74 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose74.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose74.frame.negative) i.val = (pose74.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose74.frame.negative i then (4 : Int) else 0) = pose74.anchor i + 1) i

theorem pose75_generated : GeneratedContact P7 pose75 := by
  have hA : Proper pose75.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose75 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose75.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose75.frame.negative) i.val = (pose75.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose75.frame.negative i then (4 : Int) else 0) = pose75.anchor i + 1) i

theorem pose77_generated : GeneratedContact P7 pose77 := by
  have hA : Proper pose77.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose77 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose77.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose77.frame.negative) i.val = (pose77.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose77.frame.negative i then (4 : Int) else 0) = pose77.anchor i + 1) i

theorem pose79_generated : GeneratedContact P7 pose79 := by
  have hA : Proper pose79.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose79 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose79.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose79.frame.negative) i.val = (pose79.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose79.frame.negative i then (4 : Int) else 0) = pose79.anchor i + 1) i

theorem pose82_generated : GeneratedContact P7 pose82 := by
  have hA : Proper pose82.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose82 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose82.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose82.frame.negative) i.val = (pose82.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose82.frame.negative i then (4 : Int) else 0) = pose82.anchor i + 1) i

theorem pose89_generated : GeneratedContact P7 pose89 := by
  have hA : Proper pose89.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose89 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose89.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose89.frame.negative) i.val = (pose89.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose89.frame.negative i then (4 : Int) else 0) = pose89.anchor i + 1) i

theorem pose90_generated : GeneratedContact P7 pose90 := by
  have hA : Proper pose90.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose90 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose90.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose90.frame.negative) i.val = (pose90.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose90.frame.negative i then (4 : Int) else 0) = pose90.anchor i + 1) i

theorem pose92_generated : GeneratedContact P7 pose92 := by
  have hA : Proper pose92.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose92 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose92.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose92.frame.negative) i.val = (pose92.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose92.frame.negative i then (4 : Int) else 0) = pose92.anchor i + 1) i

theorem pose99_generated : GeneratedContact P7 pose99 := by
  have hA : Proper pose99.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose99 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose99.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose99.frame.negative) i.val = (pose99.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose99.frame.negative i then (4 : Int) else 0) = pose99.anchor i + 1) i

theorem pose103_generated : GeneratedContact P7 pose103 := by
  have hA : Proper pose103.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose103 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose103.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose103.frame.negative) i.val = (pose103.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose103.frame.negative i then (4 : Int) else 0) = pose103.anchor i + 1) i

theorem pose106_generated : GeneratedContact P7 pose106 := by
  have hA : Proper pose106.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose106 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose106.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose106.frame.negative) i.val = (pose106.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose106.frame.negative i then (4 : Int) else 0) = pose106.anchor i + 1) i

theorem pose107_generated : GeneratedContact P7 pose107 := by
  have hA : Proper pose107.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose107 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose107.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose107.frame.negative) i.val = (pose107.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose107.frame.negative i then (4 : Int) else 0) = pose107.anchor i + 1) i

theorem pose110_generated : GeneratedContact P7 pose110 := by
  have hA : Proper pose110.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose110 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose110.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose110.frame.negative) i.val = (pose110.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose110.frame.negative i then (4 : Int) else 0) = pose110.anchor i + 1) i

theorem pose113_generated : GeneratedContact P7 pose113 := by
  have hA : Proper pose113.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose113 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose113.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose113.frame.negative) i.val = (pose113.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose113.frame.negative i then (4 : Int) else 0) = pose113.anchor i + 1) i

theorem pose116_generated : GeneratedContact P7 pose116 := by
  have hA : Proper pose116.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose116 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose116.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose116.frame.negative) i.val = (pose116.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose116.frame.negative i then (4 : Int) else 0) = pose116.anchor i + 1) i

theorem pose117_generated : GeneratedContact P7 pose117 := by
  have hA : Proper pose117.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose117 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose117.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose117.frame.negative) i.val = (pose117.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose117.frame.negative i then (4 : Int) else 0) = pose117.anchor i + 1) i

theorem pose122_generated : GeneratedContact P7 pose122 := by
  have hA : Proper pose122.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose122 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose122.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose122.frame.negative) i.val = (pose122.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose122.frame.negative i then (4 : Int) else 0) = pose122.anchor i + 1) i

theorem pose128_generated : GeneratedContact P7 pose128 := by
  have hA : Proper pose128.frame.negative := ⟨⟨5, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose128 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose128.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose128.frame.negative) i.val = (pose128.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose128.frame.negative i then (4 : Int) else 0) = pose128.anchor i + 1) i

theorem pose131_generated : GeneratedContact P7 pose131 := by
  have hA : Proper pose131.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose131 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose131.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose131.frame.negative) i.val = (pose131.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose131.frame.negative i then (4 : Int) else 0) = pose131.anchor i + 1) i

theorem pose137_generated : GeneratedContact P7 pose137 := by
  have hA : Proper pose137.frame.negative := ⟨⟨5, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose137 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose137.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose137.frame.negative) i.val = (pose137.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose137.frame.negative i then (4 : Int) else 0) = pose137.anchor i + 1) i

theorem pose140_generated : GeneratedContact P7 pose140 := by
  have hA : Proper pose140.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose140 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose140.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose140.frame.negative) i.val = (pose140.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose140.frame.negative i then (4 : Int) else 0) = pose140.anchor i + 1) i

theorem pose143_generated : GeneratedContact P7 pose143 := by
  have hA : Proper pose143.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose143 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose143.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose143.frame.negative) i.val = (pose143.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose143.frame.negative i then (4 : Int) else 0) = pose143.anchor i + 1) i

theorem pose144_generated : GeneratedContact P7 pose144 := by
  have hA : Proper pose144.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose144 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose144.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose144.frame.negative) i.val = (pose144.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose144.frame.negative i then (4 : Int) else 0) = pose144.anchor i + 1) i

theorem pose151_generated : GeneratedContact P7 pose151 := by
  have hA : Proper pose151.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose151 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose151.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose151.frame.negative) i.val = (pose151.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose151.frame.negative i then (4 : Int) else 0) = pose151.anchor i + 1) i

theorem pose152_generated : GeneratedContact P7 pose152 := by
  have hA : Proper pose152.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose152 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose152.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose152.frame.negative) i.val = (pose152.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose152.frame.negative i then (4 : Int) else 0) = pose152.anchor i + 1) i

theorem pose154_generated : GeneratedContact P7 pose154 := by
  have hA : Proper pose154.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose154 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose154.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose154.frame.negative) i.val = (pose154.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose154.frame.negative i then (4 : Int) else 0) = pose154.anchor i + 1) i

theorem pose157_generated : GeneratedContact P7 pose157 := by
  have hA : Proper pose157.frame.negative := ⟨⟨6, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose157 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose157.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose157.frame.negative) i.val = (pose157.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose157.frame.negative i then (4 : Int) else 0) = pose157.anchor i + 1) i

theorem pose167_generated : GeneratedContact P7 pose167 := by
  have hA : Proper pose167.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose167 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose167.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose167.frame.negative) i.val = (pose167.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose167.frame.negative i then (4 : Int) else 0) = pose167.anchor i + 1) i

theorem pose168_generated : GeneratedContact P7 pose168 := by
  have hA : Proper pose168.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose168 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose168.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose168.frame.negative) i.val = (pose168.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose168.frame.negative i then (4 : Int) else 0) = pose168.anchor i + 1) i

theorem pose169_generated : GeneratedContact P7 pose169 := by
  have hA : Proper pose169.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose169 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose169.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose169.frame.negative) i.val = (pose169.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose169.frame.negative i then (4 : Int) else 0) = pose169.anchor i + 1) i

theorem pose170_generated : GeneratedContact P7 pose170 := by
  have hA : Proper pose170.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose170 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose170.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose170.frame.negative) i.val = (pose170.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose170.frame.negative i then (4 : Int) else 0) = pose170.anchor i + 1) i

theorem pose172_generated : GeneratedContact P7 pose172 := by
  have hA : Proper pose172.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose172 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose172.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose172.frame.negative) i.val = (pose172.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose172.frame.negative i then (4 : Int) else 0) = pose172.anchor i + 1) i

theorem pose178_generated : GeneratedContact P7 pose178 := by
  have hA : Proper pose178.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose178 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose178.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose178.frame.negative) i.val = (pose178.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose178.frame.negative i then (4 : Int) else 0) = pose178.anchor i + 1) i

theorem pose183_generated : GeneratedContact P7 pose183 := by
  have hA : Proper pose183.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose183 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose183.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose183.frame.negative) i.val = (pose183.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose183.frame.negative i then (4 : Int) else 0) = pose183.anchor i + 1) i

theorem pose185_generated : GeneratedContact P7 pose185 := by
  have hA : Proper pose185.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose185 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose185.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose185.frame.negative) i.val = (pose185.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose185.frame.negative i then (4 : Int) else 0) = pose185.anchor i + 1) i

theorem pose186_generated : GeneratedContact P7 pose186 := by
  have hA : Proper pose186.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose186 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose186.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose186.frame.negative) i.val = (pose186.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose186.frame.negative i then (4 : Int) else 0) = pose186.anchor i + 1) i

theorem pose188_generated : GeneratedContact P7 pose188 := by
  have hA : Proper pose188.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose188 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose188.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose188.frame.negative) i.val = (pose188.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose188.frame.negative i then (4 : Int) else 0) = pose188.anchor i + 1) i

theorem pose190_generated : GeneratedContact P7 pose190 := by
  have hA : Proper pose190.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose190 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose190.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose190.frame.negative) i.val = (pose190.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose190.frame.negative i then (4 : Int) else 0) = pose190.anchor i + 1) i

theorem pose200_generated : GeneratedContact P7 pose200 := by
  have hA : Proper pose200.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose200 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose200.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose200.frame.negative) i.val = (pose200.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose200.frame.negative i then (4 : Int) else 0) = pose200.anchor i + 1) i

theorem pose206_generated : GeneratedContact P7 pose206 := by
  have hA : Proper pose206.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose206 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose206.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose206.frame.negative) i.val = (pose206.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose206.frame.negative i then (4 : Int) else 0) = pose206.anchor i + 1) i

theorem pose208_generated : GeneratedContact P7 pose208 := by
  have hA : Proper pose208.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose208 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose208.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose208.frame.negative) i.val = (pose208.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose208.frame.negative i then (4 : Int) else 0) = pose208.anchor i + 1) i

theorem pose210_generated : GeneratedContact P7 pose210 := by
  have hA : Proper pose210.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose210 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose210.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose210.frame.negative) i.val = (pose210.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose210.frame.negative i then (4 : Int) else 0) = pose210.anchor i + 1) i

theorem pose212_generated : GeneratedContact P7 pose212 := by
  have hA : Proper pose212.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose212 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose212.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose212.frame.negative) i.val = (pose212.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose212.frame.negative i then (4 : Int) else 0) = pose212.anchor i + 1) i

theorem pose215_generated : GeneratedContact P7 pose215 := by
  have hA : Proper pose215.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose215 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose215.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose215.frame.negative) i.val = (pose215.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose215.frame.negative i then (4 : Int) else 0) = pose215.anchor i + 1) i

theorem pose218_generated : GeneratedContact P7 pose218 := by
  have hA : Proper pose218.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose218 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose218.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose218.frame.negative) i.val = (pose218.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose218.frame.negative i then (4 : Int) else 0) = pose218.anchor i + 1) i

theorem pose223_generated : GeneratedContact P7 pose223 := by
  have hA : Proper pose223.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose223 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose223.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose223.frame.negative) i.val = (pose223.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose223.frame.negative i then (4 : Int) else 0) = pose223.anchor i + 1) i

theorem pose226_generated : GeneratedContact P7 pose226 := by
  have hA : Proper pose226.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose226 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose226.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose226.frame.negative) i.val = (pose226.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose226.frame.negative i then (4 : Int) else 0) = pose226.anchor i + 1) i

theorem pose228_generated : GeneratedContact P7 pose228 := by
  have hA : Proper pose228.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose228 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose228.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose228.frame.negative) i.val = (pose228.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose228.frame.negative i then (4 : Int) else 0) = pose228.anchor i + 1) i

theorem pose230_generated : GeneratedContact P7 pose230 := by
  have hA : Proper pose230.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose230 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose230.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose230.frame.negative) i.val = (pose230.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose230.frame.negative i then (4 : Int) else 0) = pose230.anchor i + 1) i

theorem pose232_generated : GeneratedContact P7 pose232 := by
  have hA : Proper pose232.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose232 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose232.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose232.frame.negative) i.val = (pose232.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose232.frame.negative i then (4 : Int) else 0) = pose232.anchor i + 1) i

theorem pose234_generated : GeneratedContact P7 pose234 := by
  have hA : Proper pose234.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose234 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose234.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose234.frame.negative) i.val = (pose234.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose234.frame.negative i then (4 : Int) else 0) = pose234.anchor i + 1) i

theorem pose236_generated : GeneratedContact P7 pose236 := by
  have hA : Proper pose236.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose236 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose236.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose236.frame.negative) i.val = (pose236.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose236.frame.negative i then (4 : Int) else 0) = pose236.anchor i + 1) i

theorem pose238_generated : GeneratedContact P7 pose238 := by
  have hA : Proper pose238.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose238 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hmask : pose238.frame.negative = (fun _ => false) := by apply funext; decide
    simp only [arithmeticChild, childIndex, childFrame, hmask, empty_outer_frame]
    exact (by decide : ∀ i : Fin 7, (1 * i.val) % 7 = (pose238.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose238.frame.negative i then (4 : Int) else 0) = pose238.anchor i + 1) i

theorem pose242_generated : GeneratedContact P7 pose242 := by
  have hA : Proper pose242.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose242 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose242.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose242.frame.negative) i.val = (pose242.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose242.frame.negative i then (4 : Int) else 0) = pose242.anchor i + 1) i

theorem pose255_generated : GeneratedContact P7 pose255 := by
  have hA : Proper pose255.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose255 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose255.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose255.frame.negative) i.val = (pose255.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose255.frame.negative i then (4 : Int) else 0) = pose255.anchor i + 1) i

theorem pose258_generated : GeneratedContact P7 pose258 := by
  have hA : Proper pose258.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose258 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose258.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose258.frame.negative) i.val = (pose258.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose258.frame.negative i then (4 : Int) else 0) = pose258.anchor i + 1) i

theorem pose261_generated : GeneratedContact P7 pose261 := by
  have hA : Proper pose261.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose261 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose261.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose261.frame.negative) i.val = (pose261.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose261.frame.negative i then (4 : Int) else 0) = pose261.anchor i + 1) i

theorem pose262_generated : GeneratedContact P7 pose262 := by
  have hA : Proper pose262.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose262 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose262.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose262.frame.negative) i.val = (pose262.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose262.frame.negative i then (4 : Int) else 0) = pose262.anchor i + 1) i

theorem pose263_generated : GeneratedContact P7 pose263 := by
  have hA : Proper pose263.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose263 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose263.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose263.frame.negative) i.val = (pose263.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose263.frame.negative i then (4 : Int) else 0) = pose263.anchor i + 1) i

theorem pose264_generated : GeneratedContact P7 pose264 := by
  have hA : Proper pose264.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose264 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose264.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose264.frame.negative) i.val = (pose264.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose264.frame.negative i then (4 : Int) else 0) = pose264.anchor i + 1) i

theorem pose266_generated : GeneratedContact P7 pose266 := by
  have hA : Proper pose266.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose266 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose266.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose266.frame.negative) i.val = (pose266.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose266.frame.negative i then (4 : Int) else 0) = pose266.anchor i + 1) i

theorem pose274_generated : GeneratedContact P7 pose274 := by
  have hA : Proper pose274.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose274 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose274.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose274.frame.negative) i.val = (pose274.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose274.frame.negative i then (4 : Int) else 0) = pose274.anchor i + 1) i

theorem pose275_generated : GeneratedContact P7 pose275 := by
  have hA : Proper pose275.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose275 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose275.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose275.frame.negative) i.val = (pose275.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose275.frame.negative i then (4 : Int) else 0) = pose275.anchor i + 1) i

theorem pose281_generated : GeneratedContact P7 pose281 := by
  have hA : Proper pose281.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose281 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose281.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose281.frame.negative) i.val = (pose281.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose281.frame.negative i then (4 : Int) else 0) = pose281.anchor i + 1) i

theorem pose283_generated : GeneratedContact P7 pose283 := by
  have hA : Proper pose283.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose283 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose283.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose283.frame.negative) i.val = (pose283.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose283.frame.negative i then (4 : Int) else 0) = pose283.anchor i + 1) i

theorem pose284_generated : GeneratedContact P7 pose284 := by
  have hA : Proper pose284.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose284 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose284.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose284.frame.negative) i.val = (pose284.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose284.frame.negative i then (4 : Int) else 0) = pose284.anchor i + 1) i

theorem pose287_generated : GeneratedContact P7 pose287 := by
  have hA : Proper pose287.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose287 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose287.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose287.frame.negative) i.val = (pose287.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose287.frame.negative i then (4 : Int) else 0) = pose287.anchor i + 1) i

theorem pose288_generated : GeneratedContact P7 pose288 := by
  have hA : Proper pose288.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose288 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose288.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose288.frame.negative) i.val = (pose288.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose288.frame.negative i then (4 : Int) else 0) = pose288.anchor i + 1) i

theorem pose291_generated : GeneratedContact P7 pose291 := by
  have hA : Proper pose291.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose291 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose291.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose291.frame.negative) i.val = (pose291.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose291.frame.negative i then (4 : Int) else 0) = pose291.anchor i + 1) i

theorem pose292_generated : GeneratedContact P7 pose292 := by
  have hA : Proper pose292.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose292 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose292.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose292.frame.negative) i.val = (pose292.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose292.frame.negative i then (4 : Int) else 0) = pose292.anchor i + 1) i

theorem pose294_generated : GeneratedContact P7 pose294 := by
  have hA : Proper pose294.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose294 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose294.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose294.frame.negative) i.val = (pose294.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose294.frame.negative i then (4 : Int) else 0) = pose294.anchor i + 1) i

theorem pose303_generated : GeneratedContact P7 pose303 := by
  have hA : Proper pose303.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose303 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose303.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose303.frame.negative) i.val = (pose303.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose303.frame.negative i then (4 : Int) else 0) = pose303.anchor i + 1) i

theorem pose309_generated : GeneratedContact P7 pose309 := by
  have hA : Proper pose309.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose309 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose309.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose309.frame.negative) i.val = (pose309.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose309.frame.negative i then (4 : Int) else 0) = pose309.anchor i + 1) i

theorem pose311_generated : GeneratedContact P7 pose311 := by
  have hA : Proper pose311.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose311 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose311.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose311.frame.negative) i.val = (pose311.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose311.frame.negative i then (4 : Int) else 0) = pose311.anchor i + 1) i

theorem pose313_generated : GeneratedContact P7 pose313 := by
  have hA : Proper pose313.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose313 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose313.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose313.frame.negative) i.val = (pose313.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose313.frame.negative i then (4 : Int) else 0) = pose313.anchor i + 1) i

theorem pose314_generated : GeneratedContact P7 pose314 := by
  have hA : Proper pose314.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose314 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose314.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose314.frame.negative) i.val = (pose314.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose314.frame.negative i then (4 : Int) else 0) = pose314.anchor i + 1) i

theorem pose316_generated : GeneratedContact P7 pose316 := by
  have hA : Proper pose316.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose316 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose316.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose316.frame.negative) i.val = (pose316.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose316.frame.negative i then (4 : Int) else 0) = pose316.anchor i + 1) i

theorem pose319_generated : GeneratedContact P7 pose319 := by
  have hA : Proper pose319.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose319 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose319.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose319.frame.negative) i.val = (pose319.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose319.frame.negative i then (4 : Int) else 0) = pose319.anchor i + 1) i

theorem pose325_generated : GeneratedContact P7 pose325 := by
  have hA : Proper pose325.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose325 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose325.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose325.frame.negative) i.val = (pose325.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose325.frame.negative i then (4 : Int) else 0) = pose325.anchor i + 1) i

theorem pose327_generated : GeneratedContact P7 pose327 := by
  have hA : Proper pose327.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose327 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose327.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose327.frame.negative) i.val = (pose327.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose327.frame.negative i then (4 : Int) else 0) = pose327.anchor i + 1) i

theorem pose329_generated : GeneratedContact P7 pose329 := by
  have hA : Proper pose329.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose329 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose329.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose329.frame.negative) i.val = (pose329.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose329.frame.negative i then (4 : Int) else 0) = pose329.anchor i + 1) i

theorem pose333_generated : GeneratedContact P7 pose333 := by
  have hA : Proper pose333.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose333 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose333.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose333.frame.negative) i.val = (pose333.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose333.frame.negative i then (4 : Int) else 0) = pose333.anchor i + 1) i

theorem pose334_generated : GeneratedContact P7 pose334 := by
  have hA : Proper pose334.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose334 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose334.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose334.frame.negative) i.val = (pose334.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose334.frame.negative i then (4 : Int) else 0) = pose334.anchor i + 1) i

theorem pose337_generated : GeneratedContact P7 pose337 := by
  have hA : Proper pose337.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose337 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose337.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose337.frame.negative) i.val = (pose337.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose337.frame.negative i then (4 : Int) else 0) = pose337.anchor i + 1) i

theorem pose340_generated : GeneratedContact P7 pose340 := by
  have hA : Proper pose340.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose340 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose340.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose340.frame.negative) i.val = (pose340.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose340.frame.negative i then (4 : Int) else 0) = pose340.anchor i + 1) i

theorem pose342_generated : GeneratedContact P7 pose342 := by
  have hA : Proper pose342.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose342 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose342.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose342.frame.negative) i.val = (pose342.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose342.frame.negative i then (4 : Int) else 0) = pose342.anchor i + 1) i

theorem pose343_generated : GeneratedContact P7 pose343 := by
  have hA : Proper pose343.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose343 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose343.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose343.frame.negative) i.val = (pose343.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose343.frame.negative i then (4 : Int) else 0) = pose343.anchor i + 1) i

theorem pose345_generated : GeneratedContact P7 pose345 := by
  have hA : Proper pose345.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose345 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose345.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose345.frame.negative) i.val = (pose345.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose345.frame.negative i then (4 : Int) else 0) = pose345.anchor i + 1) i

theorem pose348_generated : GeneratedContact P7 pose348 := by
  have hA : Proper pose348.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose348 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose348.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose348.frame.negative) i.val = (pose348.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose348.frame.negative i then (4 : Int) else 0) = pose348.anchor i + 1) i

theorem pose353_generated : GeneratedContact P7 pose353 := by
  have hA : Proper pose353.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose353 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose353.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose353.frame.negative) i.val = (pose353.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose353.frame.negative i then (4 : Int) else 0) = pose353.anchor i + 1) i

theorem pose361_generated : GeneratedContact P7 pose361 := by
  have hA : Proper pose361.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose361 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose361.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose361.frame.negative) i.val = (pose361.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose361.frame.negative i then (4 : Int) else 0) = pose361.anchor i + 1) i

theorem pose362_generated : GeneratedContact P7 pose362 := by
  have hA : Proper pose362.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose362 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose362.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose362.frame.negative) i.val = (pose362.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose362.frame.negative i then (4 : Int) else 0) = pose362.anchor i + 1) i

theorem pose364_generated : GeneratedContact P7 pose364 := by
  have hA : Proper pose364.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose364 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose364.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose364.frame.negative) i.val = (pose364.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose364.frame.negative i then (4 : Int) else 0) = pose364.anchor i + 1) i

theorem pose366_generated : GeneratedContact P7 pose366 := by
  have hA : Proper pose366.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose366 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose366.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose366.frame.negative) i.val = (pose366.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose366.frame.negative i then (4 : Int) else 0) = pose366.anchor i + 1) i

theorem pose367_generated : GeneratedContact P7 pose367 := by
  have hA : Proper pose367.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose367 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose367.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose367.frame.negative) i.val = (pose367.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose367.frame.negative i then (4 : Int) else 0) = pose367.anchor i + 1) i

theorem pose372_generated : GeneratedContact P7 pose372 := by
  have hA : Proper pose372.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose372 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose372.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose372.frame.negative) i.val = (pose372.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose372.frame.negative i then (4 : Int) else 0) = pose372.anchor i + 1) i

theorem pose374_generated : GeneratedContact P7 pose374 := by
  have hA : Proper pose374.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose374 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose374.frame.negative := ⟨⟨5, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose374.frame.negative) i.val = (pose374.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose374.frame.negative i then (4 : Int) else 0) = pose374.anchor i + 1) i

theorem pose378_generated : GeneratedContact P7 pose378 := by
  have hA : Proper pose378.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose378 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose378.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose378.frame.negative) i.val = (pose378.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose378.frame.negative i then (4 : Int) else 0) = pose378.anchor i + 1) i

theorem pose381_generated : GeneratedContact P7 pose381 := by
  have hA : Proper pose381.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose381 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose381.frame.negative := ⟨⟨5, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose381.frame.negative) i.val = (pose381.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose381.frame.negative i then (4 : Int) else 0) = pose381.anchor i + 1) i

theorem pose382_generated : GeneratedContact P7 pose382 := by
  have hA : Proper pose382.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose382 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose382.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose382.frame.negative) i.val = (pose382.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose382.frame.negative i then (4 : Int) else 0) = pose382.anchor i + 1) i

theorem pose384_generated : GeneratedContact P7 pose384 := by
  have hA : Proper pose384.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose384 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose384.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose384.frame.negative) i.val = (pose384.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose384.frame.negative i then (4 : Int) else 0) = pose384.anchor i + 1) i

theorem pose389_generated : GeneratedContact P7 pose389 := by
  have hA : Proper pose389.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose389 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose389.frame.negative := ⟨⟨1, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose389.frame.negative) i.val = (pose389.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose389.frame.negative i then (4 : Int) else 0) = pose389.anchor i + 1) i

theorem pose395_generated : GeneratedContact P7 pose395 := by
  have hA : Proper pose395.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose395 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose395.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose395.frame.negative) i.val = (pose395.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose395.frame.negative i then (4 : Int) else 0) = pose395.anchor i + 1) i

theorem pose397_generated : GeneratedContact P7 pose397 := by
  have hA : Proper pose397.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose397 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose397.frame.negative := ⟨⟨3, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose397.frame.negative) i.val = (pose397.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose397.frame.negative i then (4 : Int) else 0) = pose397.anchor i + 1) i

theorem pose398_generated : GeneratedContact P7 pose398 := by
  have hA : Proper pose398.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose398 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose398.frame.negative := ⟨⟨4, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose398.frame.negative) i.val = (pose398.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose398.frame.negative i then (4 : Int) else 0) = pose398.anchor i + 1) i

theorem pose399_generated : GeneratedContact P7 pose399 := by
  have hA : Proper pose399.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose399 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose399.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose399.frame.negative) i.val = (pose399.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose399.frame.negative i then (4 : Int) else 0) = pose399.anchor i + 1) i

theorem pose400_generated : GeneratedContact P7 pose400 := by
  have hA : Proper pose400.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose400 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose400.frame.negative := ⟨⟨2, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose400.frame.negative) i.val = (pose400.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose400.frame.negative i then (4 : Int) else 0) = pose400.anchor i + 1) i

theorem pose406_generated : GeneratedContact P7 pose406 := by
  have hA : Proper pose406.frame.negative := ⟨⟨0, by decide⟩, by decide⟩
  apply generated_of_exact_outer_child pose406 hA
  apply Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    have hn : NonemptyMask pose406.frame.negative := ⟨⟨6, by decide⟩, by decide⟩
    rw [outer_index_value P7 _ hA hn]
    exact (by decide : ∀ i : Fin 7, Uniform.lamPerm 7 1 6
      (extendMask pose406.frame.negative) i.val = (pose406.frame.perm i).val) i
  · intro i
    rw [child_outer_negative]
    rfl
  · intro i
    rw [child_outer_anchor]
    exact (by decide : ∀ i : Fin 7, (if pose406.frame.negative i then (4 : Int) else 0) = pose406.anchor i + 1) i

#print axioms pose2_generated
end CompactT7Preparation
