import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 184 through 199. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass184 : massAt 185 = 2 * nestedSum 184 massAt 184 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed184 : packedAt 185 = (1 + digitBase) * nestedSum 184 packedAt 184 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign184 : SignCertificate 184 := by decide +kernel
private theorem checked184 : IndexCertificate 184 := ⟨mass184, packed184, fun _ => sign184⟩

private theorem mass185 : massAt 186 = 2 * nestedSum 185 massAt 185 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed185 : packedAt 186 = (1 + digitBase) * nestedSum 185 packedAt 185 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign185 : SignCertificate 185 := by decide +kernel
private theorem checked185 : IndexCertificate 185 := ⟨mass185, packed185, fun _ => sign185⟩

private theorem mass186 : massAt 187 = 2 * nestedSum 186 massAt 186 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed186 : packedAt 187 = (1 + digitBase) * nestedSum 186 packedAt 186 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign186 : SignCertificate 186 := by decide +kernel
private theorem checked186 : IndexCertificate 186 := ⟨mass186, packed186, fun _ => sign186⟩

private theorem mass187 : massAt 188 = 2 * nestedSum 187 massAt 187 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed187 : packedAt 188 = (1 + digitBase) * nestedSum 187 packedAt 187 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign187 : SignCertificate 187 := by decide +kernel
private theorem checked187 : IndexCertificate 187 := ⟨mass187, packed187, fun _ => sign187⟩

private theorem mass188 : massAt 189 = 2 * nestedSum 188 massAt 188 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed188 : packedAt 189 = (1 + digitBase) * nestedSum 188 packedAt 188 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign188 : SignCertificate 188 := by decide +kernel
private theorem checked188 : IndexCertificate 188 := ⟨mass188, packed188, fun _ => sign188⟩

private theorem mass189 : massAt 190 = 2 * nestedSum 189 massAt 189 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed189 : packedAt 190 = (1 + digitBase) * nestedSum 189 packedAt 189 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign189 : SignCertificate 189 := by decide +kernel
private theorem checked189 : IndexCertificate 189 := ⟨mass189, packed189, fun _ => sign189⟩

private theorem mass190 : massAt 191 = 2 * nestedSum 190 massAt 190 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed190 : packedAt 191 = (1 + digitBase) * nestedSum 190 packedAt 190 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign190 : SignCertificate 190 := by decide +kernel
private theorem checked190 : IndexCertificate 190 := ⟨mass190, packed190, fun _ => sign190⟩

private theorem mass191 : massAt 192 = 2 * nestedSum 191 massAt 191 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed191 : packedAt 192 = (1 + digitBase) * nestedSum 191 packedAt 191 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign191 : SignCertificate 191 := by decide +kernel
private theorem checked191 : IndexCertificate 191 := ⟨mass191, packed191, fun _ => sign191⟩

private theorem mass192 : massAt 193 = 2 * nestedSum 192 massAt 192 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed192 : packedAt 193 = (1 + digitBase) * nestedSum 192 packedAt 192 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign192 : SignCertificate 192 := by decide +kernel
private theorem checked192 : IndexCertificate 192 := ⟨mass192, packed192, fun _ => sign192⟩

private theorem mass193 : massAt 194 = 2 * nestedSum 193 massAt 193 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed193 : packedAt 194 = (1 + digitBase) * nestedSum 193 packedAt 193 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign193 : SignCertificate 193 := by decide +kernel
private theorem checked193 : IndexCertificate 193 := ⟨mass193, packed193, fun _ => sign193⟩

private theorem mass194 : massAt 195 = 2 * nestedSum 194 massAt 194 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed194 : packedAt 195 = (1 + digitBase) * nestedSum 194 packedAt 194 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign194 : SignCertificate 194 := by decide +kernel
private theorem checked194 : IndexCertificate 194 := ⟨mass194, packed194, fun _ => sign194⟩

private theorem mass195 : massAt 196 = 2 * nestedSum 195 massAt 195 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed195 : packedAt 196 = (1 + digitBase) * nestedSum 195 packedAt 195 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign195 : SignCertificate 195 := by decide +kernel
private theorem checked195 : IndexCertificate 195 := ⟨mass195, packed195, fun _ => sign195⟩

private theorem mass196 : massAt 197 = 2 * nestedSum 196 massAt 196 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed196 : packedAt 197 = (1 + digitBase) * nestedSum 196 packedAt 196 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign196 : SignCertificate 196 := by decide +kernel
private theorem checked196 : IndexCertificate 196 := ⟨mass196, packed196, fun _ => sign196⟩

private theorem mass197 : massAt 198 = 2 * nestedSum 197 massAt 197 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed197 : packedAt 198 = (1 + digitBase) * nestedSum 197 packedAt 197 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign197 : SignCertificate 197 := by decide +kernel
private theorem checked197 : IndexCertificate 197 := ⟨mass197, packed197, fun _ => sign197⟩

private theorem mass198 : massAt 199 = 2 * nestedSum 198 massAt 198 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed198 : packedAt 199 = (1 + digitBase) * nestedSum 198 packedAt 198 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign198 : SignCertificate 198 := by decide +kernel
private theorem checked198 : IndexCertificate 198 := ⟨mass198, packed198, fun _ => sign198⟩

private theorem mass199 : massAt 200 = 2 * nestedSum 199 massAt 199 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed199 : packedAt 200 = (1 + digitBase) * nestedSum 199 packedAt 199 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign199 : SignCertificate 199 := by decide +kernel
private theorem checked199 : IndexCertificate 199 := ⟨mass199, packed199, fun _ => sign199⟩

theorem certificates184To199 (n : ℕ) (hn : 184 ≤ n) (hn' : n ≤ 199) : IndexCertificate n := by
  interval_cases n
  · exact checked184
  · exact checked185
  · exact checked186
  · exact checked187
  · exact checked188
  · exact checked189
  · exact checked190
  · exact checked191
  · exact checked192
  · exact checked193
  · exact checked194
  · exact checked195
  · exact checked196
  · exact checked197
  · exact checked198
  · exact checked199

end PlanePartition
