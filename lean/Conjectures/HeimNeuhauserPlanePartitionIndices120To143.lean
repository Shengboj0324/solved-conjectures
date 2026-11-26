import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 120 through 143. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass120 : massAt 121 = 2 * nestedSum 120 massAt 120 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed120 : packedAt 121 = (1 + digitBase) * nestedSum 120 packedAt 120 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign120 : SignCertificate 120 := by decide +kernel
private theorem checked120 : IndexCertificate 120 := ⟨mass120, packed120, fun _ => sign120⟩

private theorem mass121 : massAt 122 = 2 * nestedSum 121 massAt 121 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed121 : packedAt 122 = (1 + digitBase) * nestedSum 121 packedAt 121 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign121 : SignCertificate 121 := by decide +kernel
private theorem checked121 : IndexCertificate 121 := ⟨mass121, packed121, fun _ => sign121⟩

private theorem mass122 : massAt 123 = 2 * nestedSum 122 massAt 122 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed122 : packedAt 123 = (1 + digitBase) * nestedSum 122 packedAt 122 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign122 : SignCertificate 122 := by decide +kernel
private theorem checked122 : IndexCertificate 122 := ⟨mass122, packed122, fun _ => sign122⟩

private theorem mass123 : massAt 124 = 2 * nestedSum 123 massAt 123 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed123 : packedAt 124 = (1 + digitBase) * nestedSum 123 packedAt 123 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign123 : SignCertificate 123 := by decide +kernel
private theorem checked123 : IndexCertificate 123 := ⟨mass123, packed123, fun _ => sign123⟩

private theorem mass124 : massAt 125 = 2 * nestedSum 124 massAt 124 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed124 : packedAt 125 = (1 + digitBase) * nestedSum 124 packedAt 124 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign124 : SignCertificate 124 := by decide +kernel
private theorem checked124 : IndexCertificate 124 := ⟨mass124, packed124, fun _ => sign124⟩

private theorem mass125 : massAt 126 = 2 * nestedSum 125 massAt 125 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed125 : packedAt 126 = (1 + digitBase) * nestedSum 125 packedAt 125 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign125 : SignCertificate 125 := by decide +kernel
private theorem checked125 : IndexCertificate 125 := ⟨mass125, packed125, fun _ => sign125⟩

private theorem mass126 : massAt 127 = 2 * nestedSum 126 massAt 126 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed126 : packedAt 127 = (1 + digitBase) * nestedSum 126 packedAt 126 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign126 : SignCertificate 126 := by decide +kernel
private theorem checked126 : IndexCertificate 126 := ⟨mass126, packed126, fun _ => sign126⟩

private theorem mass127 : massAt 128 = 2 * nestedSum 127 massAt 127 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed127 : packedAt 128 = (1 + digitBase) * nestedSum 127 packedAt 127 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign127 : SignCertificate 127 := by decide +kernel
private theorem checked127 : IndexCertificate 127 := ⟨mass127, packed127, fun _ => sign127⟩

private theorem mass128 : massAt 129 = 2 * nestedSum 128 massAt 128 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed128 : packedAt 129 = (1 + digitBase) * nestedSum 128 packedAt 128 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign128 : SignCertificate 128 := by decide +kernel
private theorem checked128 : IndexCertificate 128 := ⟨mass128, packed128, fun _ => sign128⟩

private theorem mass129 : massAt 130 = 2 * nestedSum 129 massAt 129 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed129 : packedAt 130 = (1 + digitBase) * nestedSum 129 packedAt 129 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign129 : SignCertificate 129 := by decide +kernel
private theorem checked129 : IndexCertificate 129 := ⟨mass129, packed129, fun _ => sign129⟩

private theorem mass130 : massAt 131 = 2 * nestedSum 130 massAt 130 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed130 : packedAt 131 = (1 + digitBase) * nestedSum 130 packedAt 130 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign130 : SignCertificate 130 := by decide +kernel
private theorem checked130 : IndexCertificate 130 := ⟨mass130, packed130, fun _ => sign130⟩

private theorem mass131 : massAt 132 = 2 * nestedSum 131 massAt 131 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed131 : packedAt 132 = (1 + digitBase) * nestedSum 131 packedAt 131 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign131 : SignCertificate 131 := by decide +kernel
private theorem checked131 : IndexCertificate 131 := ⟨mass131, packed131, fun _ => sign131⟩

private theorem mass132 : massAt 133 = 2 * nestedSum 132 massAt 132 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed132 : packedAt 133 = (1 + digitBase) * nestedSum 132 packedAt 132 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign132 : SignCertificate 132 := by decide +kernel
private theorem checked132 : IndexCertificate 132 := ⟨mass132, packed132, fun _ => sign132⟩

private theorem mass133 : massAt 134 = 2 * nestedSum 133 massAt 133 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed133 : packedAt 134 = (1 + digitBase) * nestedSum 133 packedAt 133 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign133 : SignCertificate 133 := by decide +kernel
private theorem checked133 : IndexCertificate 133 := ⟨mass133, packed133, fun _ => sign133⟩

private theorem mass134 : massAt 135 = 2 * nestedSum 134 massAt 134 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed134 : packedAt 135 = (1 + digitBase) * nestedSum 134 packedAt 134 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign134 : SignCertificate 134 := by decide +kernel
private theorem checked134 : IndexCertificate 134 := ⟨mass134, packed134, fun _ => sign134⟩

private theorem mass135 : massAt 136 = 2 * nestedSum 135 massAt 135 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed135 : packedAt 136 = (1 + digitBase) * nestedSum 135 packedAt 135 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign135 : SignCertificate 135 := by decide +kernel
private theorem checked135 : IndexCertificate 135 := ⟨mass135, packed135, fun _ => sign135⟩

private theorem mass136 : massAt 137 = 2 * nestedSum 136 massAt 136 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed136 : packedAt 137 = (1 + digitBase) * nestedSum 136 packedAt 136 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign136 : SignCertificate 136 := by decide +kernel
private theorem checked136 : IndexCertificate 136 := ⟨mass136, packed136, fun _ => sign136⟩

private theorem mass137 : massAt 138 = 2 * nestedSum 137 massAt 137 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed137 : packedAt 138 = (1 + digitBase) * nestedSum 137 packedAt 137 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign137 : SignCertificate 137 := by decide +kernel
private theorem checked137 : IndexCertificate 137 := ⟨mass137, packed137, fun _ => sign137⟩

private theorem mass138 : massAt 139 = 2 * nestedSum 138 massAt 138 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed138 : packedAt 139 = (1 + digitBase) * nestedSum 138 packedAt 138 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign138 : SignCertificate 138 := by decide +kernel
private theorem checked138 : IndexCertificate 138 := ⟨mass138, packed138, fun _ => sign138⟩

private theorem mass139 : massAt 140 = 2 * nestedSum 139 massAt 139 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed139 : packedAt 140 = (1 + digitBase) * nestedSum 139 packedAt 139 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign139 : SignCertificate 139 := by decide +kernel
private theorem checked139 : IndexCertificate 139 := ⟨mass139, packed139, fun _ => sign139⟩

private theorem mass140 : massAt 141 = 2 * nestedSum 140 massAt 140 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed140 : packedAt 141 = (1 + digitBase) * nestedSum 140 packedAt 140 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign140 : SignCertificate 140 := by decide +kernel
private theorem checked140 : IndexCertificate 140 := ⟨mass140, packed140, fun _ => sign140⟩

private theorem mass141 : massAt 142 = 2 * nestedSum 141 massAt 141 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed141 : packedAt 142 = (1 + digitBase) * nestedSum 141 packedAt 141 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign141 : SignCertificate 141 := by decide +kernel
private theorem checked141 : IndexCertificate 141 := ⟨mass141, packed141, fun _ => sign141⟩

private theorem mass142 : massAt 143 = 2 * nestedSum 142 massAt 142 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed142 : packedAt 143 = (1 + digitBase) * nestedSum 142 packedAt 142 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign142 : SignCertificate 142 := by decide +kernel
private theorem checked142 : IndexCertificate 142 := ⟨mass142, packed142, fun _ => sign142⟩

private theorem mass143 : massAt 144 = 2 * nestedSum 143 massAt 143 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed143 : packedAt 144 = (1 + digitBase) * nestedSum 143 packedAt 143 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign143 : SignCertificate 143 := by decide +kernel
private theorem checked143 : IndexCertificate 143 := ⟨mass143, packed143, fun _ => sign143⟩

theorem certificates120To143 (n : ℕ) (hn : 120 ≤ n) (hn' : n ≤ 143) : IndexCertificate n := by
  interval_cases n
  · exact checked120
  · exact checked121
  · exact checked122
  · exact checked123
  · exact checked124
  · exact checked125
  · exact checked126
  · exact checked127
  · exact checked128
  · exact checked129
  · exact checked130
  · exact checked131
  · exact checked132
  · exact checked133
  · exact checked134
  · exact checked135
  · exact checked136
  · exact checked137
  · exact checked138
  · exact checked139
  · exact checked140
  · exact checked141
  · exact checked142
  · exact checked143

end PlanePartition
