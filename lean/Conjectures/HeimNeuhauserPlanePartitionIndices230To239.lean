import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 230 through 239. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass230 : massAt 231 = 2 * nestedSum 230 massAt 230 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed230 : packedAt 231 = (1 + digitBase) * nestedSum 230 packedAt 230 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign230 : SignCertificate 230 := by decide +kernel
private theorem checked230 : IndexCertificate 230 := ⟨mass230, packed230, fun _ => sign230⟩

private theorem mass231 : massAt 232 = 2 * nestedSum 231 massAt 231 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed231 : packedAt 232 = (1 + digitBase) * nestedSum 231 packedAt 231 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign231 : SignCertificate 231 := by decide +kernel
private theorem checked231 : IndexCertificate 231 := ⟨mass231, packed231, fun _ => sign231⟩

private theorem mass232 : massAt 233 = 2 * nestedSum 232 massAt 232 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed232 : packedAt 233 = (1 + digitBase) * nestedSum 232 packedAt 232 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign232 : SignCertificate 232 := by decide +kernel
private theorem checked232 : IndexCertificate 232 := ⟨mass232, packed232, fun _ => sign232⟩

private theorem mass233 : massAt 234 = 2 * nestedSum 233 massAt 233 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed233 : packedAt 234 = (1 + digitBase) * nestedSum 233 packedAt 233 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign233 : SignCertificate 233 := by decide +kernel
private theorem checked233 : IndexCertificate 233 := ⟨mass233, packed233, fun _ => sign233⟩

private theorem mass234 : massAt 235 = 2 * nestedSum 234 massAt 234 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed234 : packedAt 235 = (1 + digitBase) * nestedSum 234 packedAt 234 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign234 : SignCertificate 234 := by decide +kernel
private theorem checked234 : IndexCertificate 234 := ⟨mass234, packed234, fun _ => sign234⟩

private theorem mass235 : massAt 236 = 2 * nestedSum 235 massAt 235 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed235 : packedAt 236 = (1 + digitBase) * nestedSum 235 packedAt 235 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign235 : SignCertificate 235 := by decide +kernel
private theorem checked235 : IndexCertificate 235 := ⟨mass235, packed235, fun _ => sign235⟩

private theorem mass236 : massAt 237 = 2 * nestedSum 236 massAt 236 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed236 : packedAt 237 = (1 + digitBase) * nestedSum 236 packedAt 236 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign236 : SignCertificate 236 := by decide +kernel
private theorem checked236 : IndexCertificate 236 := ⟨mass236, packed236, fun _ => sign236⟩

private theorem mass237 : massAt 238 = 2 * nestedSum 237 massAt 237 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed237 : packedAt 238 = (1 + digitBase) * nestedSum 237 packedAt 237 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign237 : SignCertificate 237 := by decide +kernel
private theorem checked237 : IndexCertificate 237 := ⟨mass237, packed237, fun _ => sign237⟩

private theorem mass238 : massAt 239 = 2 * nestedSum 238 massAt 238 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed238 : packedAt 239 = (1 + digitBase) * nestedSum 238 packedAt 238 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign238 : SignCertificate 238 := by decide +kernel
private theorem checked238 : IndexCertificate 238 := ⟨mass238, packed238, fun _ => sign238⟩

private theorem mass239 : massAt 240 = 2 * nestedSum 239 massAt 239 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed239 : packedAt 240 = (1 + digitBase) * nestedSum 239 packedAt 239 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign239 : SignCertificate 239 := by decide +kernel
private theorem checked239 : IndexCertificate 239 := ⟨mass239, packed239, fun _ => sign239⟩

theorem certificates230To239 (n : ℕ) (hn : 230 ≤ n) (hn' : n ≤ 239) : IndexCertificate n := by
  interval_cases n
  · exact checked230
  · exact checked231
  · exact checked232
  · exact checked233
  · exact checked234
  · exact checked235
  · exact checked236
  · exact checked237
  · exact checked238
  · exact checked239

end PlanePartition
