import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 200 through 214. -/

namespace PlanePartition

-- Release each completed kernel decision before elaborating the next certificate.
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass200 : massAt 201 = 2 * nestedSum 200 massAt 200 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed200 : packedAt 201 = (1 + digitBase) * nestedSum 200 packedAt 200 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign200 : SignCertificate 200 := by decide +kernel
private theorem checked200 : IndexCertificate 200 := ⟨mass200, packed200, fun _ => sign200⟩

private theorem mass201 : massAt 202 = 2 * nestedSum 201 massAt 201 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed201 : packedAt 202 = (1 + digitBase) * nestedSum 201 packedAt 201 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign201 : SignCertificate 201 := by decide +kernel
private theorem checked201 : IndexCertificate 201 := ⟨mass201, packed201, fun _ => sign201⟩

private theorem mass202 : massAt 203 = 2 * nestedSum 202 massAt 202 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed202 : packedAt 203 = (1 + digitBase) * nestedSum 202 packedAt 202 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign202 : SignCertificate 202 := by decide +kernel
private theorem checked202 : IndexCertificate 202 := ⟨mass202, packed202, fun _ => sign202⟩

private theorem mass203 : massAt 204 = 2 * nestedSum 203 massAt 203 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed203 : packedAt 204 = (1 + digitBase) * nestedSum 203 packedAt 203 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign203 : SignCertificate 203 := by decide +kernel
private theorem checked203 : IndexCertificate 203 := ⟨mass203, packed203, fun _ => sign203⟩

private theorem mass204 : massAt 205 = 2 * nestedSum 204 massAt 204 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed204 : packedAt 205 = (1 + digitBase) * nestedSum 204 packedAt 204 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign204 : SignCertificate 204 := by decide +kernel
private theorem checked204 : IndexCertificate 204 := ⟨mass204, packed204, fun _ => sign204⟩

private theorem mass205 : massAt 206 = 2 * nestedSum 205 massAt 205 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed205 : packedAt 206 = (1 + digitBase) * nestedSum 205 packedAt 205 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign205 : SignCertificate 205 := by decide +kernel
private theorem checked205 : IndexCertificate 205 := ⟨mass205, packed205, fun _ => sign205⟩

private theorem mass206 : massAt 207 = 2 * nestedSum 206 massAt 206 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed206 : packedAt 207 = (1 + digitBase) * nestedSum 206 packedAt 206 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign206 : SignCertificate 206 := by decide +kernel
private theorem checked206 : IndexCertificate 206 := ⟨mass206, packed206, fun _ => sign206⟩

private theorem mass207 : massAt 208 = 2 * nestedSum 207 massAt 207 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed207 : packedAt 208 = (1 + digitBase) * nestedSum 207 packedAt 207 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign207 : SignCertificate 207 := by decide +kernel
private theorem checked207 : IndexCertificate 207 := ⟨mass207, packed207, fun _ => sign207⟩

private theorem mass208 : massAt 209 = 2 * nestedSum 208 massAt 208 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed208 : packedAt 209 = (1 + digitBase) * nestedSum 208 packedAt 208 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign208 : SignCertificate 208 := by decide +kernel
private theorem checked208 : IndexCertificate 208 := ⟨mass208, packed208, fun _ => sign208⟩

private theorem mass209 : massAt 210 = 2 * nestedSum 209 massAt 209 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed209 : packedAt 210 = (1 + digitBase) * nestedSum 209 packedAt 209 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign209 : SignCertificate 209 := by decide +kernel
private theorem checked209 : IndexCertificate 209 := ⟨mass209, packed209, fun _ => sign209⟩

private theorem mass210 : massAt 211 = 2 * nestedSum 210 massAt 210 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed210 : packedAt 211 = (1 + digitBase) * nestedSum 210 packedAt 210 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign210 : SignCertificate 210 := by decide +kernel
private theorem checked210 : IndexCertificate 210 := ⟨mass210, packed210, fun _ => sign210⟩

private theorem mass211 : massAt 212 = 2 * nestedSum 211 massAt 211 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed211 : packedAt 212 = (1 + digitBase) * nestedSum 211 packedAt 211 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign211 : SignCertificate 211 := by decide +kernel
private theorem checked211 : IndexCertificate 211 := ⟨mass211, packed211, fun _ => sign211⟩

private theorem mass212 : massAt 213 = 2 * nestedSum 212 massAt 212 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed212 : packedAt 213 = (1 + digitBase) * nestedSum 212 packedAt 212 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign212 : SignCertificate 212 := by decide +kernel
private theorem checked212 : IndexCertificate 212 := ⟨mass212, packed212, fun _ => sign212⟩

private theorem mass213 : massAt 214 = 2 * nestedSum 213 massAt 213 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed213 : packedAt 214 = (1 + digitBase) * nestedSum 213 packedAt 213 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign213 : SignCertificate 213 := by decide +kernel
private theorem checked213 : IndexCertificate 213 := ⟨mass213, packed213, fun _ => sign213⟩

private theorem mass214 : massAt 215 = 2 * nestedSum 214 massAt 214 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed214 : packedAt 215 = (1 + digitBase) * nestedSum 214 packedAt 214 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign214 : SignCertificate 214 := by decide +kernel
private theorem checked214 : IndexCertificate 214 := ⟨mass214, packed214, fun _ => sign214⟩

theorem certificates200To214 (n : ℕ) (hn : 200 ≤ n) (hn' : n ≤ 214) : IndexCertificate n := by
  interval_cases n
  · exact checked200
  · exact checked201
  · exact checked202
  · exact checked203
  · exact checked204
  · exact checked205
  · exact checked206
  · exact checked207
  · exact checked208
  · exact checked209
  · exact checked210
  · exact checked211
  · exact checked212
  · exact checked213
  · exact checked214

end PlanePartition
