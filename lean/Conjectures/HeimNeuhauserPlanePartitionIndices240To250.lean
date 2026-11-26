import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 240 through 250. -/

namespace PlanePartition

-- Release each completed kernel decision before elaborating the next certificate.
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass240 : massAt 241 = 2 * nestedSum 240 massAt 240 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed240 : packedAt 241 = (1 + digitBase) * nestedSum 240 packedAt 240 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign240 : SignCertificate 240 := by decide +kernel
private theorem checked240 : IndexCertificate 240 := ⟨mass240, packed240, fun _ => sign240⟩

private theorem mass241 : massAt 242 = 2 * nestedSum 241 massAt 241 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed241 : packedAt 242 = (1 + digitBase) * nestedSum 241 packedAt 241 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign241 : SignCertificate 241 := by decide +kernel
private theorem checked241 : IndexCertificate 241 := ⟨mass241, packed241, fun _ => sign241⟩

private theorem mass242 : massAt 243 = 2 * nestedSum 242 massAt 242 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed242 : packedAt 243 = (1 + digitBase) * nestedSum 242 packedAt 242 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign242 : SignCertificate 242 := by decide +kernel
private theorem checked242 : IndexCertificate 242 := ⟨mass242, packed242, fun _ => sign242⟩

private theorem mass243 : massAt 244 = 2 * nestedSum 243 massAt 243 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed243 : packedAt 244 = (1 + digitBase) * nestedSum 243 packedAt 243 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign243 : SignCertificate 243 := by decide +kernel
private theorem checked243 : IndexCertificate 243 := ⟨mass243, packed243, fun _ => sign243⟩

private theorem mass244 : massAt 245 = 2 * nestedSum 244 massAt 244 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed244 : packedAt 245 = (1 + digitBase) * nestedSum 244 packedAt 244 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign244 : SignCertificate 244 := by decide +kernel
private theorem checked244 : IndexCertificate 244 := ⟨mass244, packed244, fun _ => sign244⟩

private theorem mass245 : massAt 246 = 2 * nestedSum 245 massAt 245 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed245 : packedAt 246 = (1 + digitBase) * nestedSum 245 packedAt 245 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign245 : SignCertificate 245 := by decide +kernel
private theorem checked245 : IndexCertificate 245 := ⟨mass245, packed245, fun _ => sign245⟩

private theorem mass246 : massAt 247 = 2 * nestedSum 246 massAt 246 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed246 : packedAt 247 = (1 + digitBase) * nestedSum 246 packedAt 246 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign246 : SignCertificate 246 := by decide +kernel
private theorem checked246 : IndexCertificate 246 := ⟨mass246, packed246, fun _ => sign246⟩

private theorem mass247 : massAt 248 = 2 * nestedSum 247 massAt 247 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed247 : packedAt 248 = (1 + digitBase) * nestedSum 247 packedAt 247 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign247 : SignCertificate 247 := by decide +kernel
private theorem checked247 : IndexCertificate 247 := ⟨mass247, packed247, fun _ => sign247⟩

private theorem mass248 : massAt 249 = 2 * nestedSum 248 massAt 248 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed248 : packedAt 249 = (1 + digitBase) * nestedSum 248 packedAt 248 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign248 : SignCertificate 248 := by decide +kernel
private theorem checked248 : IndexCertificate 248 := ⟨mass248, packed248, fun _ => sign248⟩

private theorem mass249 : massAt 250 = 2 * nestedSum 249 massAt 249 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed249 : packedAt 250 = (1 + digitBase) * nestedSum 249 packedAt 249 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign249 : SignCertificate 249 := by decide +kernel
private theorem checked249 : IndexCertificate 249 := ⟨mass249, packed249, fun _ => sign249⟩

private theorem mass250 : massAt 251 = 2 * nestedSum 250 massAt 250 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed250 : packedAt 251 = (1 + digitBase) * nestedSum 250 packedAt 250 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign250 : SignCertificate 250 := by decide +kernel
private theorem checked250 : IndexCertificate 250 := ⟨mass250, packed250, fun _ => sign250⟩

theorem certificates240To250 (n : ℕ) (hn : 240 ≤ n) (hn' : n ≤ 250) : IndexCertificate n := by
  interval_cases n
  · exact checked240
  · exact checked241
  · exact checked242
  · exact checked243
  · exact checked244
  · exact checked245
  · exact checked246
  · exact checked247
  · exact checked248
  · exact checked249
  · exact checked250

end PlanePartition
