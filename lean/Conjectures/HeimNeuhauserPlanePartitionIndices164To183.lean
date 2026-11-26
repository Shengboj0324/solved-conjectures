import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 164 through 183. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass164 : massAt 165 = 2 * nestedSum 164 massAt 164 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed164 : packedAt 165 = (1 + digitBase) * nestedSum 164 packedAt 164 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign164 : SignCertificate 164 := by decide +kernel
private theorem checked164 : IndexCertificate 164 := ⟨mass164, packed164, fun _ => sign164⟩

private theorem mass165 : massAt 166 = 2 * nestedSum 165 massAt 165 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed165 : packedAt 166 = (1 + digitBase) * nestedSum 165 packedAt 165 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign165 : SignCertificate 165 := by decide +kernel
private theorem checked165 : IndexCertificate 165 := ⟨mass165, packed165, fun _ => sign165⟩

private theorem mass166 : massAt 167 = 2 * nestedSum 166 massAt 166 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed166 : packedAt 167 = (1 + digitBase) * nestedSum 166 packedAt 166 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign166 : SignCertificate 166 := by decide +kernel
private theorem checked166 : IndexCertificate 166 := ⟨mass166, packed166, fun _ => sign166⟩

private theorem mass167 : massAt 168 = 2 * nestedSum 167 massAt 167 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed167 : packedAt 168 = (1 + digitBase) * nestedSum 167 packedAt 167 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign167 : SignCertificate 167 := by decide +kernel
private theorem checked167 : IndexCertificate 167 := ⟨mass167, packed167, fun _ => sign167⟩

private theorem mass168 : massAt 169 = 2 * nestedSum 168 massAt 168 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed168 : packedAt 169 = (1 + digitBase) * nestedSum 168 packedAt 168 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign168 : SignCertificate 168 := by decide +kernel
private theorem checked168 : IndexCertificate 168 := ⟨mass168, packed168, fun _ => sign168⟩

private theorem mass169 : massAt 170 = 2 * nestedSum 169 massAt 169 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed169 : packedAt 170 = (1 + digitBase) * nestedSum 169 packedAt 169 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign169 : SignCertificate 169 := by decide +kernel
private theorem checked169 : IndexCertificate 169 := ⟨mass169, packed169, fun _ => sign169⟩

private theorem mass170 : massAt 171 = 2 * nestedSum 170 massAt 170 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed170 : packedAt 171 = (1 + digitBase) * nestedSum 170 packedAt 170 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign170 : SignCertificate 170 := by decide +kernel
private theorem checked170 : IndexCertificate 170 := ⟨mass170, packed170, fun _ => sign170⟩

private theorem mass171 : massAt 172 = 2 * nestedSum 171 massAt 171 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed171 : packedAt 172 = (1 + digitBase) * nestedSum 171 packedAt 171 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign171 : SignCertificate 171 := by decide +kernel
private theorem checked171 : IndexCertificate 171 := ⟨mass171, packed171, fun _ => sign171⟩

private theorem mass172 : massAt 173 = 2 * nestedSum 172 massAt 172 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed172 : packedAt 173 = (1 + digitBase) * nestedSum 172 packedAt 172 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign172 : SignCertificate 172 := by decide +kernel
private theorem checked172 : IndexCertificate 172 := ⟨mass172, packed172, fun _ => sign172⟩

private theorem mass173 : massAt 174 = 2 * nestedSum 173 massAt 173 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed173 : packedAt 174 = (1 + digitBase) * nestedSum 173 packedAt 173 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign173 : SignCertificate 173 := by decide +kernel
private theorem checked173 : IndexCertificate 173 := ⟨mass173, packed173, fun _ => sign173⟩

private theorem mass174 : massAt 175 = 2 * nestedSum 174 massAt 174 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed174 : packedAt 175 = (1 + digitBase) * nestedSum 174 packedAt 174 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign174 : SignCertificate 174 := by decide +kernel
private theorem checked174 : IndexCertificate 174 := ⟨mass174, packed174, fun _ => sign174⟩

private theorem mass175 : massAt 176 = 2 * nestedSum 175 massAt 175 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed175 : packedAt 176 = (1 + digitBase) * nestedSum 175 packedAt 175 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign175 : SignCertificate 175 := by decide +kernel
private theorem checked175 : IndexCertificate 175 := ⟨mass175, packed175, fun _ => sign175⟩

private theorem mass176 : massAt 177 = 2 * nestedSum 176 massAt 176 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed176 : packedAt 177 = (1 + digitBase) * nestedSum 176 packedAt 176 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign176 : SignCertificate 176 := by decide +kernel
private theorem checked176 : IndexCertificate 176 := ⟨mass176, packed176, fun _ => sign176⟩

private theorem mass177 : massAt 178 = 2 * nestedSum 177 massAt 177 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed177 : packedAt 178 = (1 + digitBase) * nestedSum 177 packedAt 177 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign177 : SignCertificate 177 := by decide +kernel
private theorem checked177 : IndexCertificate 177 := ⟨mass177, packed177, fun _ => sign177⟩

private theorem mass178 : massAt 179 = 2 * nestedSum 178 massAt 178 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed178 : packedAt 179 = (1 + digitBase) * nestedSum 178 packedAt 178 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign178 : SignCertificate 178 := by decide +kernel
private theorem checked178 : IndexCertificate 178 := ⟨mass178, packed178, fun _ => sign178⟩

private theorem mass179 : massAt 180 = 2 * nestedSum 179 massAt 179 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed179 : packedAt 180 = (1 + digitBase) * nestedSum 179 packedAt 179 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign179 : SignCertificate 179 := by decide +kernel
private theorem checked179 : IndexCertificate 179 := ⟨mass179, packed179, fun _ => sign179⟩

private theorem mass180 : massAt 181 = 2 * nestedSum 180 massAt 180 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed180 : packedAt 181 = (1 + digitBase) * nestedSum 180 packedAt 180 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign180 : SignCertificate 180 := by decide +kernel
private theorem checked180 : IndexCertificate 180 := ⟨mass180, packed180, fun _ => sign180⟩

private theorem mass181 : massAt 182 = 2 * nestedSum 181 massAt 181 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed181 : packedAt 182 = (1 + digitBase) * nestedSum 181 packedAt 181 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign181 : SignCertificate 181 := by decide +kernel
private theorem checked181 : IndexCertificate 181 := ⟨mass181, packed181, fun _ => sign181⟩

private theorem mass182 : massAt 183 = 2 * nestedSum 182 massAt 182 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed182 : packedAt 183 = (1 + digitBase) * nestedSum 182 packedAt 182 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign182 : SignCertificate 182 := by decide +kernel
private theorem checked182 : IndexCertificate 182 := ⟨mass182, packed182, fun _ => sign182⟩

private theorem mass183 : massAt 184 = 2 * nestedSum 183 massAt 183 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed183 : packedAt 184 = (1 + digitBase) * nestedSum 183 packedAt 183 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign183 : SignCertificate 183 := by decide +kernel
private theorem checked183 : IndexCertificate 183 := ⟨mass183, packed183, fun _ => sign183⟩

theorem certificates164To183 (n : ℕ) (hn : 164 ≤ n) (hn' : n ≤ 183) : IndexCertificate n := by
  interval_cases n
  · exact checked164
  · exact checked165
  · exact checked166
  · exact checked167
  · exact checked168
  · exact checked169
  · exact checked170
  · exact checked171
  · exact checked172
  · exact checked173
  · exact checked174
  · exact checked175
  · exact checked176
  · exact checked177
  · exact checked178
  · exact checked179
  · exact checked180
  · exact checked181
  · exact checked182
  · exact checked183

end PlanePartition
