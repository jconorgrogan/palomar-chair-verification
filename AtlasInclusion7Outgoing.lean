module
public import AtlasInclusion7Incoming
@[expose] public section
namespace CompactT7Preparation
open RegisteredPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem pose0_generated : GeneratedContact P7 pose0 := by
  have he : pose0 = pose3.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose3_generated

theorem pose1_generated : GeneratedContact P7 pose1 := by
  have he : pose1 = pose25.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose25_generated

theorem pose4_generated : GeneratedContact P7 pose4 := by
  have he : pose4 = pose28.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose28_generated

theorem pose13_generated : GeneratedContact P7 pose13 := by
  have he : pose13 = pose167.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose167_generated

theorem pose23_generated : GeneratedContact P7 pose23 := by
  have he : pose23 = pose275.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose275_generated

theorem pose24_generated : GeneratedContact P7 pose24 := by
  have he : pose24 = pose382.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose382_generated

theorem pose26_generated : GeneratedContact P7 pose26 := by
  have he : pose26 = pose384.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose384_generated

theorem pose27_generated : GeneratedContact P7 pose27 := by
  have he : pose27 = pose399.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose399_generated

theorem pose29_generated : GeneratedContact P7 pose29 := by
  have he : pose29 = pose406.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose406_generated

theorem pose39_generated : GeneratedContact P7 pose39 := by
  have he : pose39 = pose151.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose151_generated

theorem pose46_generated : GeneratedContact P7 pose46 := by
  have he : pose46 = pose52.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose52_generated

theorem pose47_generated : GeneratedContact P7 pose47 := by
  have he : pose47 = pose364.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose364_generated

theorem pose48_generated : GeneratedContact P7 pose48 := by
  have he : pose48 = pose372.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose372_generated

theorem pose49_generated : GeneratedContact P7 pose49 := by
  have he : pose49 = pose45.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose45_generated

theorem pose50_generated : GeneratedContact P7 pose50 := by
  have he : pose50 = pose54.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose54_generated

theorem pose53_generated : GeneratedContact P7 pose53 := by
  have he : pose53 = pose366.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose366_generated

theorem pose55_generated : GeneratedContact P7 pose55 := by
  have he : pose55 = pose374.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose374_generated

theorem pose59_generated : GeneratedContact P7 pose59 := by
  have he : pose59 = pose284.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose284_generated

theorem pose71_generated : GeneratedContact P7 pose71 := by
  have he : pose71 = pose309.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose309_generated

theorem pose76_generated : GeneratedContact P7 pose76 := by
  have he : pose76 = pose342.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose342_generated

theorem pose78_generated : GeneratedContact P7 pose78 := by
  have he : pose78 = pose77.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose77_generated

theorem pose80_generated : GeneratedContact P7 pose80 := by
  have he : pose80 = pose345.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose345_generated

theorem pose81_generated : GeneratedContact P7 pose81 := by
  have he : pose81 = pose75.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose75_generated

theorem pose83_generated : GeneratedContact P7 pose83 := by
  have he : pose83 = pose343.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose343_generated

theorem pose84_generated : GeneratedContact P7 pose84 := by
  have he : pose84 = pose79.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose79_generated

theorem pose85_generated : GeneratedContact P7 pose85 := by
  have he : pose85 = pose348.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose348_generated

theorem pose91_generated : GeneratedContact P7 pose91 := by
  have he : pose91 = pose122.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose122_generated

theorem pose102_generated : GeneratedContact P7 pose102 := by
  have he : pose102 = pose90.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose90_generated

theorem pose108_generated : GeneratedContact P7 pose108 := by
  have he : pose108 = pose311.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose311_generated

theorem pose109_generated : GeneratedContact P7 pose109 := by
  have he : pose109 = pose113.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose113_generated

theorem pose111_generated : GeneratedContact P7 pose111 := by
  have he : pose111 = pose316.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose316_generated

theorem pose112_generated : GeneratedContact P7 pose112 := by
  have he : pose112 = pose110.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose110_generated

theorem pose114_generated : GeneratedContact P7 pose114 := by
  have he : pose114 = pose314.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose314_generated

theorem pose115_generated : GeneratedContact P7 pose115 := by
  have he : pose115 = pose116.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose116_generated

theorem pose118_generated : GeneratedContact P7 pose118 := by
  have he : pose118 = pose319.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose319_generated

theorem pose123_generated : GeneratedContact P7 pose123 := by
  have he : pose123 = pose333.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose333_generated

theorem pose134_generated : GeneratedContact P7 pose134 := by
  have he : pose134 = pose378.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose378_generated

theorem pose138_generated : GeneratedContact P7 pose138 := by
  have he : pose138 = pose137.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose137_generated

theorem pose139_generated : GeneratedContact P7 pose139 := by
  have he : pose139 = pose287.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose287_generated

theorem pose141_generated : GeneratedContact P7 pose141 := by
  have he : pose141 = pose288.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose288_generated

theorem pose142_generated : GeneratedContact P7 pose142 := by
  have he : pose142 = pose143.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose143_generated

theorem pose145_generated : GeneratedContact P7 pose145 := by
  have he : pose145 = pose144.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose144_generated

theorem pose146_generated : GeneratedContact P7 pose146 := by
  have he : pose146 = pose291.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose291_generated

theorem pose147_generated : GeneratedContact P7 pose147 := by
  have he : pose147 = pose292.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose292_generated

theorem pose153_generated : GeneratedContact P7 pose153 := by
  have he : pose153 = pose40.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose40_generated

theorem pose164_generated : GeneratedContact P7 pose164 := by
  have he : pose164 = pose389.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose389_generated

theorem pose171_generated : GeneratedContact P7 pose171 := by
  have he : pose171 = pose169.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose169_generated

theorem pose173_generated : GeneratedContact P7 pose173 := by
  have he : pose173 = pose170.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose170_generated

theorem pose174_generated : GeneratedContact P7 pose174 := by
  have he : pose174 = pose172.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose172_generated

theorem pose175_generated : GeneratedContact P7 pose175 := by
  have he : pose175 = pose261.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose261_generated

theorem pose176_generated : GeneratedContact P7 pose176 := by
  have he : pose176 = pose262.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose262_generated

theorem pose177_generated : GeneratedContact P7 pose177 := by
  have he : pose177 = pose263.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose263_generated

theorem pose179_generated : GeneratedContact P7 pose179 := by
  have he : pose179 = pose264.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose264_generated

theorem pose184_generated : GeneratedContact P7 pose184 := by
  have he : pose184 = pose16.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose16_generated

theorem pose187_generated : GeneratedContact P7 pose187 := by
  have he : pose187 = pose186.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose186_generated

theorem pose189_generated : GeneratedContact P7 pose189 := by
  have he : pose189 = pose188.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose188_generated

theorem pose191_generated : GeneratedContact P7 pose191 := by
  have he : pose191 = pose190.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose190_generated

theorem pose201_generated : GeneratedContact P7 pose201 := by
  have he : pose201 = pose200.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose200_generated

theorem pose207_generated : GeneratedContact P7 pose207 := by
  have he : pose207 = pose206.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose206_generated

theorem pose209_generated : GeneratedContact P7 pose209 := by
  have he : pose209 = pose208.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose208_generated

theorem pose211_generated : GeneratedContact P7 pose211 := by
  have he : pose211 = pose210.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose210_generated

theorem pose213_generated : GeneratedContact P7 pose213 := by
  have he : pose213 = pose212.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose212_generated

theorem pose216_generated : GeneratedContact P7 pose216 := by
  have he : pose216 = pose215.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose215_generated

theorem pose219_generated : GeneratedContact P7 pose219 := by
  have he : pose219 = pose242.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose242_generated

theorem pose224_generated : GeneratedContact P7 pose224 := by
  have he : pose224 = pose223.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose223_generated

theorem pose227_generated : GeneratedContact P7 pose227 := by
  have he : pose227 = pose226.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose226_generated

theorem pose229_generated : GeneratedContact P7 pose229 := by
  have he : pose229 = pose228.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose228_generated

theorem pose231_generated : GeneratedContact P7 pose231 := by
  have he : pose231 = pose230.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose230_generated

theorem pose233_generated : GeneratedContact P7 pose233 := by
  have he : pose233 = pose232.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose232_generated

theorem pose235_generated : GeneratedContact P7 pose235 := by
  have he : pose235 = pose234.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose234_generated

theorem pose237_generated : GeneratedContact P7 pose237 := by
  have he : pose237 = pose236.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose236_generated

theorem pose239_generated : GeneratedContact P7 pose239 := by
  have he : pose239 = pose238.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose238_generated

theorem pose243_generated : GeneratedContact P7 pose243 := by
  have he : pose243 = pose218.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose218_generated

theorem pose253_generated : GeneratedContact P7 pose253 := by
  have he : pose253 = pose19.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose19_generated

theorem pose256_generated : GeneratedContact P7 pose256 := by
  have he : pose256 = pose20.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose20_generated

theorem pose257_generated : GeneratedContact P7 pose257 := by
  have he : pose257 = pose21.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose21_generated

theorem pose259_generated : GeneratedContact P7 pose259 := by
  have he : pose259 = pose22.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose22_generated

theorem pose260_generated : GeneratedContact P7 pose260 := by
  have he : pose260 = pose178.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose178_generated

theorem pose268_generated : GeneratedContact P7 pose268 := by
  have he : pose268 = pose266.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose266_generated

theorem pose273_generated : GeneratedContact P7 pose273 := by
  have he : pose273 = pose395.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose395_generated

theorem pose276_generated : GeneratedContact P7 pose276 := by
  have he : pose276 = pose397.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose397_generated

theorem pose277_generated : GeneratedContact P7 pose277 := by
  have he : pose277 = pose398.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose398_generated

theorem pose279_generated : GeneratedContact P7 pose279 := by
  have he : pose279 = pose43.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose43_generated

theorem pose282_generated : GeneratedContact P7 pose282 := by
  have he : pose282 = pose44.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose44_generated

theorem pose285_generated : GeneratedContact P7 pose285 := by
  have he : pose285 = pose361.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose361_generated

theorem pose286_generated : GeneratedContact P7 pose286 := by
  have he : pose286 = pose362.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose362_generated

theorem pose289_generated : GeneratedContact P7 pose289 := by
  have he : pose289 = pose140.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose140_generated

theorem pose295_generated : GeneratedContact P7 pose295 := by
  have he : pose295 = pose294.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose294_generated

theorem pose300_generated : GeneratedContact P7 pose300 := by
  have he : pose300 = pose60.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose60_generated

theorem pose301_generated : GeneratedContact P7 pose301 := by
  have he : pose301 = pose61.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose61_generated

theorem pose302_generated : GeneratedContact P7 pose302 := by
  have he : pose302 = pose381.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose381_generated

theorem pose305_generated : GeneratedContact P7 pose305 := by
  have he : pose305 = pose70.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose70_generated

theorem pose307_generated : GeneratedContact P7 pose307 := by
  have he : pose307 = pose334.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose334_generated

theorem pose308_generated : GeneratedContact P7 pose308 := by
  have he : pose308 = pose89.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose89_generated

theorem pose310_generated : GeneratedContact P7 pose310 := by
  have he : pose310 = pose353.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose353_generated

theorem pose312_generated : GeneratedContact P7 pose312 := by
  have he : pose312 = pose313.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose313_generated

theorem pose318_generated : GeneratedContact P7 pose318 := by
  have he : pose318 = pose117.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose117_generated

theorem pose324_generated : GeneratedContact P7 pose324 := by
  have he : pose324 = pose74.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose74_generated

theorem pose326_generated : GeneratedContact P7 pose326 := by
  have he : pose326 = pose337.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose337_generated

theorem pose328_generated : GeneratedContact P7 pose328 := by
  have he : pose328 = pose92.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose92_generated

theorem pose331_generated : GeneratedContact P7 pose331 := by
  have he : pose331 = pose99.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose99_generated

theorem pose335_generated : GeneratedContact P7 pose335 := by
  have he : pose335 = pose325.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose325_generated

theorem pose336_generated : GeneratedContact P7 pose336 := by
  have he : pose336 = pose106.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose106_generated

theorem pose338_generated : GeneratedContact P7 pose338 := by
  have he : pose338 = pose329.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose329_generated

theorem pose339_generated : GeneratedContact P7 pose339 := by
  have he : pose339 = pose82.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose82_generated

theorem pose346_generated : GeneratedContact P7 pose346 := by
  have he : pose346 = pose340.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose340_generated

theorem pose352_generated : GeneratedContact P7 pose352 := by
  have he : pose352 = pose103.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose103_generated

theorem pose354_generated : GeneratedContact P7 pose354 := by
  have he : pose354 = pose327.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose327_generated

theorem pose355_generated : GeneratedContact P7 pose355 := by
  have he : pose355 = pose107.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose107_generated

theorem pose357_generated : GeneratedContact P7 pose357 := by
  have he : pose357 = pose128.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose128_generated

theorem pose359_generated : GeneratedContact P7 pose359 := by
  have he : pose359 = pose152.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose152_generated

theorem pose360_generated : GeneratedContact P7 pose360 := by
  have he : pose360 = pose281.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose281_generated

theorem pose363_generated : GeneratedContact P7 pose363 := by
  have he : pose363 = pose303.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose303_generated

theorem pose365_generated : GeneratedContact P7 pose365 := by
  have he : pose365 = pose367.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose367_generated

theorem pose370_generated : GeneratedContact P7 pose370 := by
  have he : pose370 = pose51.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose51_generated

theorem pose377_generated : GeneratedContact P7 pose377 := by
  have he : pose377 = pose131.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose131_generated

theorem pose379_generated : GeneratedContact P7 pose379 := by
  have he : pose379 = pose154.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose154_generated

theorem pose380_generated : GeneratedContact P7 pose380 := by
  have he : pose380 = pose283.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose283_generated

theorem pose383_generated : GeneratedContact P7 pose383 := by
  have he : pose383 = pose400.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose400_generated

theorem pose387_generated : GeneratedContact P7 pose387 := by
  have he : pose387 = pose157.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose157_generated

theorem pose390_generated : GeneratedContact P7 pose390 := by
  have he : pose390 = pose168.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose168_generated

theorem pose391_generated : GeneratedContact P7 pose391 := by
  have he : pose391 = pose183.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose183_generated

theorem pose392_generated : GeneratedContact P7 pose392 := by
  have he : pose392 = pose185.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose185_generated

theorem pose393_generated : GeneratedContact P7 pose393 := by
  have he : pose393 = pose255.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose255_generated

theorem pose394_generated : GeneratedContact P7 pose394 := by
  have he : pose394 = pose258.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose258_generated

theorem pose396_generated : GeneratedContact P7 pose396 := by
  have he : pose396 = pose274.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose274_generated

theorem pose402_generated : GeneratedContact P7 pose402 := by
  have he : pose402 = pose2.inv := by
    apply Pose.Same.eq
    exact ⟨by decide, by decide, by decide⟩
  rw [he]
  exact generated_inverse P7 _ pose2_generated

#print axioms pose0_generated
end CompactT7Preparation
