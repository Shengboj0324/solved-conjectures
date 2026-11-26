import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 215 through 229. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass215 : massAt 216 = 2 * nestedSum 215 massAt 215 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed215 : packedAt 216 = (1 + digitBase) * nestedSum 215 packedAt 215 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign215 : SignCertificate 215 := by decide +kernel
private theorem checked215 : IndexCertificate 215 := ⟨mass215, packed215, fun _ => sign215⟩

private theorem mass216 : massAt 217 = 2 * nestedSum 216 massAt 216 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed216 : packedAt 217 = (1 + digitBase) * nestedSum 216 packedAt 216 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign216 : SignCertificate 216 := by decide +kernel
private theorem checked216 : IndexCertificate 216 := ⟨mass216, packed216, fun _ => sign216⟩

private theorem mass217 : massAt 218 = 2 * nestedSum 217 massAt 217 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed217 : packedAt 218 = (1 + digitBase) * nestedSum 217 packedAt 217 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign217 : SignCertificate 217 := by decide +kernel
private theorem checked217 : IndexCertificate 217 := ⟨mass217, packed217, fun _ => sign217⟩

private theorem mass218 : massAt 219 = 2 * nestedSum 218 massAt 218 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed218 : packedAt 219 = (1 + digitBase) * nestedSum 218 packedAt 218 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign218 : SignCertificate 218 := by decide +kernel
private theorem checked218 : IndexCertificate 218 := ⟨mass218, packed218, fun _ => sign218⟩

private theorem mass219 : massAt 220 = 2 * nestedSum 219 massAt 219 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed219 : packedAt 220 = (1 + digitBase) * nestedSum 219 packedAt 219 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign219 : SignCertificate 219 := by decide +kernel
private theorem checked219 : IndexCertificate 219 := ⟨mass219, packed219, fun _ => sign219⟩

private theorem mass220 : massAt 221 = 2 * nestedSum 220 massAt 220 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed220 : packedAt 221 = (1 + digitBase) * nestedSum 220 packedAt 220 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign220 : SignCertificate 220 := by decide +kernel
private theorem checked220 : IndexCertificate 220 := ⟨mass220, packed220, fun _ => sign220⟩

private theorem mass221 : massAt 222 = 2 * nestedSum 221 massAt 221 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed221 : packedAt 222 = (1 + digitBase) * nestedSum 221 packedAt 221 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign221 : SignCertificate 221 := by decide +kernel
private theorem checked221 : IndexCertificate 221 := ⟨mass221, packed221, fun _ => sign221⟩

private theorem mass222 : massAt 223 = 2 * nestedSum 222 massAt 222 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed222 : packedAt 223 = (1 + digitBase) * nestedSum 222 packedAt 222 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign222 : SignCertificate 222 := by decide +kernel
private theorem checked222 : IndexCertificate 222 := ⟨mass222, packed222, fun _ => sign222⟩

private theorem mass223 : massAt 224 = 2 * nestedSum 223 massAt 223 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed223 : packedAt 224 = (1 + digitBase) * nestedSum 223 packedAt 223 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign223 : SignCertificate 223 := by decide +kernel
private theorem checked223 : IndexCertificate 223 := ⟨mass223, packed223, fun _ => sign223⟩

private theorem mass224 : massAt 225 = 2 * nestedSum 224 massAt 224 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed224 : packedAt 225 = (1 + digitBase) * nestedSum 224 packedAt 224 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign224 : SignCertificate 224 := by decide +kernel
private theorem checked224 : IndexCertificate 224 := ⟨mass224, packed224, fun _ => sign224⟩

private theorem mass225 : massAt 226 = 2 * nestedSum 225 massAt 225 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed225 : packedAt 226 = (1 + digitBase) * nestedSum 225 packedAt 225 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign225 : SignCertificate 225 := by decide +kernel
private theorem checked225 : IndexCertificate 225 := ⟨mass225, packed225, fun _ => sign225⟩

private theorem mass226 : massAt 227 = 2 * nestedSum 226 massAt 226 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed226 : packedAt 227 = (1 + digitBase) * nestedSum 226 packedAt 226 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign226 : SignCertificate 226 := by decide +kernel
private theorem checked226 : IndexCertificate 226 := ⟨mass226, packed226, fun _ => sign226⟩

private theorem mass227 : massAt 228 = 2 * nestedSum 227 massAt 227 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed227 : packedAt 228 = (1 + digitBase) * nestedSum 227 packedAt 227 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign227 : SignCertificate 227 := by decide +kernel
private theorem checked227 : IndexCertificate 227 := ⟨mass227, packed227, fun _ => sign227⟩

private theorem mass228 : massAt 229 = 2 * nestedSum 228 massAt 228 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed228 : packedAt 229 = (1 + digitBase) * nestedSum 228 packedAt 228 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign228 : SignCertificate 228 := by decide +kernel
private theorem checked228 : IndexCertificate 228 := ⟨mass228, packed228, fun _ => sign228⟩

private theorem mass229 : massAt 230 = 2 * nestedSum 229 massAt 229 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed229 : packedAt 230 = (1 + digitBase) * nestedSum 229 packedAt 229 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign229 : SignCertificate 229 := by decide +kernel
private theorem checked229 : IndexCertificate 229 := ⟨mass229, packed229, fun _ => sign229⟩

theorem certificates215To229 (n : ℕ) (hn : 215 ≤ n) (hn' : n ≤ 229) : IndexCertificate n := by
  interval_cases n
  · exact checked215
  · exact checked216
  · exact checked217
  · exact checked218
  · exact checked219
  · exact checked220
  · exact checked221
  · exact checked222
  · exact checked223
  · exact checked224
  · exact checked225
  · exact checked226
  · exact checked227
  · exact checked228
  · exact checked229

end PlanePartition
