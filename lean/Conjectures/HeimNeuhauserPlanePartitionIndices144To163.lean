import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 144 through 163. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass144 : massAt 145 = 2 * nestedSum 144 massAt 144 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed144 : packedAt 145 = (1 + digitBase) * nestedSum 144 packedAt 144 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign144 : SignCertificate 144 := by decide +kernel
private theorem checked144 : IndexCertificate 144 := ⟨mass144, packed144, fun _ => sign144⟩

private theorem mass145 : massAt 146 = 2 * nestedSum 145 massAt 145 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed145 : packedAt 146 = (1 + digitBase) * nestedSum 145 packedAt 145 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign145 : SignCertificate 145 := by decide +kernel
private theorem checked145 : IndexCertificate 145 := ⟨mass145, packed145, fun _ => sign145⟩

private theorem mass146 : massAt 147 = 2 * nestedSum 146 massAt 146 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed146 : packedAt 147 = (1 + digitBase) * nestedSum 146 packedAt 146 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign146 : SignCertificate 146 := by decide +kernel
private theorem checked146 : IndexCertificate 146 := ⟨mass146, packed146, fun _ => sign146⟩

private theorem mass147 : massAt 148 = 2 * nestedSum 147 massAt 147 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed147 : packedAt 148 = (1 + digitBase) * nestedSum 147 packedAt 147 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign147 : SignCertificate 147 := by decide +kernel
private theorem checked147 : IndexCertificate 147 := ⟨mass147, packed147, fun _ => sign147⟩

private theorem mass148 : massAt 149 = 2 * nestedSum 148 massAt 148 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed148 : packedAt 149 = (1 + digitBase) * nestedSum 148 packedAt 148 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign148 : SignCertificate 148 := by decide +kernel
private theorem checked148 : IndexCertificate 148 := ⟨mass148, packed148, fun _ => sign148⟩

private theorem mass149 : massAt 150 = 2 * nestedSum 149 massAt 149 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed149 : packedAt 150 = (1 + digitBase) * nestedSum 149 packedAt 149 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign149 : SignCertificate 149 := by decide +kernel
private theorem checked149 : IndexCertificate 149 := ⟨mass149, packed149, fun _ => sign149⟩

private theorem mass150 : massAt 151 = 2 * nestedSum 150 massAt 150 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed150 : packedAt 151 = (1 + digitBase) * nestedSum 150 packedAt 150 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign150 : SignCertificate 150 := by decide +kernel
private theorem checked150 : IndexCertificate 150 := ⟨mass150, packed150, fun _ => sign150⟩

private theorem mass151 : massAt 152 = 2 * nestedSum 151 massAt 151 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed151 : packedAt 152 = (1 + digitBase) * nestedSum 151 packedAt 151 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign151 : SignCertificate 151 := by decide +kernel
private theorem checked151 : IndexCertificate 151 := ⟨mass151, packed151, fun _ => sign151⟩

private theorem mass152 : massAt 153 = 2 * nestedSum 152 massAt 152 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed152 : packedAt 153 = (1 + digitBase) * nestedSum 152 packedAt 152 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign152 : SignCertificate 152 := by decide +kernel
private theorem checked152 : IndexCertificate 152 := ⟨mass152, packed152, fun _ => sign152⟩

private theorem mass153 : massAt 154 = 2 * nestedSum 153 massAt 153 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed153 : packedAt 154 = (1 + digitBase) * nestedSum 153 packedAt 153 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign153 : SignCertificate 153 := by decide +kernel
private theorem checked153 : IndexCertificate 153 := ⟨mass153, packed153, fun _ => sign153⟩

private theorem mass154 : massAt 155 = 2 * nestedSum 154 massAt 154 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed154 : packedAt 155 = (1 + digitBase) * nestedSum 154 packedAt 154 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign154 : SignCertificate 154 := by decide +kernel
private theorem checked154 : IndexCertificate 154 := ⟨mass154, packed154, fun _ => sign154⟩

private theorem mass155 : massAt 156 = 2 * nestedSum 155 massAt 155 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed155 : packedAt 156 = (1 + digitBase) * nestedSum 155 packedAt 155 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign155 : SignCertificate 155 := by decide +kernel
private theorem checked155 : IndexCertificate 155 := ⟨mass155, packed155, fun _ => sign155⟩

private theorem mass156 : massAt 157 = 2 * nestedSum 156 massAt 156 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed156 : packedAt 157 = (1 + digitBase) * nestedSum 156 packedAt 156 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign156 : SignCertificate 156 := by decide +kernel
private theorem checked156 : IndexCertificate 156 := ⟨mass156, packed156, fun _ => sign156⟩

private theorem mass157 : massAt 158 = 2 * nestedSum 157 massAt 157 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed157 : packedAt 158 = (1 + digitBase) * nestedSum 157 packedAt 157 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign157 : SignCertificate 157 := by decide +kernel
private theorem checked157 : IndexCertificate 157 := ⟨mass157, packed157, fun _ => sign157⟩

private theorem mass158 : massAt 159 = 2 * nestedSum 158 massAt 158 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed158 : packedAt 159 = (1 + digitBase) * nestedSum 158 packedAt 158 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign158 : SignCertificate 158 := by decide +kernel
private theorem checked158 : IndexCertificate 158 := ⟨mass158, packed158, fun _ => sign158⟩

private theorem mass159 : massAt 160 = 2 * nestedSum 159 massAt 159 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed159 : packedAt 160 = (1 + digitBase) * nestedSum 159 packedAt 159 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign159 : SignCertificate 159 := by decide +kernel
private theorem checked159 : IndexCertificate 159 := ⟨mass159, packed159, fun _ => sign159⟩

private theorem mass160 : massAt 161 = 2 * nestedSum 160 massAt 160 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed160 : packedAt 161 = (1 + digitBase) * nestedSum 160 packedAt 160 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign160 : SignCertificate 160 := by decide +kernel
private theorem checked160 : IndexCertificate 160 := ⟨mass160, packed160, fun _ => sign160⟩

private theorem mass161 : massAt 162 = 2 * nestedSum 161 massAt 161 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed161 : packedAt 162 = (1 + digitBase) * nestedSum 161 packedAt 161 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign161 : SignCertificate 161 := by decide +kernel
private theorem checked161 : IndexCertificate 161 := ⟨mass161, packed161, fun _ => sign161⟩

private theorem mass162 : massAt 163 = 2 * nestedSum 162 massAt 162 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed162 : packedAt 163 = (1 + digitBase) * nestedSum 162 packedAt 162 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign162 : SignCertificate 162 := by decide +kernel
private theorem checked162 : IndexCertificate 162 := ⟨mass162, packed162, fun _ => sign162⟩

private theorem mass163 : massAt 164 = 2 * nestedSum 163 massAt 163 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed163 : packedAt 164 = (1 + digitBase) * nestedSum 163 packedAt 163 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign163 : SignCertificate 163 := by decide +kernel
private theorem checked163 : IndexCertificate 163 := ⟨mass163, packed163, fun _ => sign163⟩

theorem certificates144To163 (n : ℕ) (hn : 144 ≤ n) (hn' : n ≤ 163) : IndexCertificate n := by
  interval_cases n
  · exact checked144
  · exact checked145
  · exact checked146
  · exact checked147
  · exact checked148
  · exact checked149
  · exact checked150
  · exact checked151
  · exact checked152
  · exact checked153
  · exact checked154
  · exact checked155
  · exact checked156
  · exact checked157
  · exact checked158
  · exact checked159
  · exact checked160
  · exact checked161
  · exact checked162
  · exact checked163

end PlanePartition
