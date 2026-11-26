import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 96 through 119. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass96 : massAt 97 = 2 * nestedSum 96 massAt 96 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed96 : packedAt 97 = (1 + digitBase) * nestedSum 96 packedAt 96 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign96 : SignCertificate 96 := by decide +kernel
private theorem checked96 : IndexCertificate 96 := ⟨mass96, packed96, fun _ => sign96⟩

private theorem mass97 : massAt 98 = 2 * nestedSum 97 massAt 97 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed97 : packedAt 98 = (1 + digitBase) * nestedSum 97 packedAt 97 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign97 : SignCertificate 97 := by decide +kernel
private theorem checked97 : IndexCertificate 97 := ⟨mass97, packed97, fun _ => sign97⟩

private theorem mass98 : massAt 99 = 2 * nestedSum 98 massAt 98 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed98 : packedAt 99 = (1 + digitBase) * nestedSum 98 packedAt 98 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign98 : SignCertificate 98 := by decide +kernel
private theorem checked98 : IndexCertificate 98 := ⟨mass98, packed98, fun _ => sign98⟩

private theorem mass99 : massAt 100 = 2 * nestedSum 99 massAt 99 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed99 : packedAt 100 = (1 + digitBase) * nestedSum 99 packedAt 99 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign99 : SignCertificate 99 := by decide +kernel
private theorem checked99 : IndexCertificate 99 := ⟨mass99, packed99, fun _ => sign99⟩

private theorem mass100 : massAt 101 = 2 * nestedSum 100 massAt 100 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed100 : packedAt 101 = (1 + digitBase) * nestedSum 100 packedAt 100 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign100 : SignCertificate 100 := by decide +kernel
private theorem checked100 : IndexCertificate 100 := ⟨mass100, packed100, fun _ => sign100⟩

private theorem mass101 : massAt 102 = 2 * nestedSum 101 massAt 101 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed101 : packedAt 102 = (1 + digitBase) * nestedSum 101 packedAt 101 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign101 : SignCertificate 101 := by decide +kernel
private theorem checked101 : IndexCertificate 101 := ⟨mass101, packed101, fun _ => sign101⟩

private theorem mass102 : massAt 103 = 2 * nestedSum 102 massAt 102 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed102 : packedAt 103 = (1 + digitBase) * nestedSum 102 packedAt 102 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign102 : SignCertificate 102 := by decide +kernel
private theorem checked102 : IndexCertificate 102 := ⟨mass102, packed102, fun _ => sign102⟩

private theorem mass103 : massAt 104 = 2 * nestedSum 103 massAt 103 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed103 : packedAt 104 = (1 + digitBase) * nestedSum 103 packedAt 103 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign103 : SignCertificate 103 := by decide +kernel
private theorem checked103 : IndexCertificate 103 := ⟨mass103, packed103, fun _ => sign103⟩

private theorem mass104 : massAt 105 = 2 * nestedSum 104 massAt 104 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed104 : packedAt 105 = (1 + digitBase) * nestedSum 104 packedAt 104 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign104 : SignCertificate 104 := by decide +kernel
private theorem checked104 : IndexCertificate 104 := ⟨mass104, packed104, fun _ => sign104⟩

private theorem mass105 : massAt 106 = 2 * nestedSum 105 massAt 105 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed105 : packedAt 106 = (1 + digitBase) * nestedSum 105 packedAt 105 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign105 : SignCertificate 105 := by decide +kernel
private theorem checked105 : IndexCertificate 105 := ⟨mass105, packed105, fun _ => sign105⟩

private theorem mass106 : massAt 107 = 2 * nestedSum 106 massAt 106 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed106 : packedAt 107 = (1 + digitBase) * nestedSum 106 packedAt 106 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign106 : SignCertificate 106 := by decide +kernel
private theorem checked106 : IndexCertificate 106 := ⟨mass106, packed106, fun _ => sign106⟩

private theorem mass107 : massAt 108 = 2 * nestedSum 107 massAt 107 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed107 : packedAt 108 = (1 + digitBase) * nestedSum 107 packedAt 107 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign107 : SignCertificate 107 := by decide +kernel
private theorem checked107 : IndexCertificate 107 := ⟨mass107, packed107, fun _ => sign107⟩

private theorem mass108 : massAt 109 = 2 * nestedSum 108 massAt 108 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed108 : packedAt 109 = (1 + digitBase) * nestedSum 108 packedAt 108 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign108 : SignCertificate 108 := by decide +kernel
private theorem checked108 : IndexCertificate 108 := ⟨mass108, packed108, fun _ => sign108⟩

private theorem mass109 : massAt 110 = 2 * nestedSum 109 massAt 109 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed109 : packedAt 110 = (1 + digitBase) * nestedSum 109 packedAt 109 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign109 : SignCertificate 109 := by decide +kernel
private theorem checked109 : IndexCertificate 109 := ⟨mass109, packed109, fun _ => sign109⟩

private theorem mass110 : massAt 111 = 2 * nestedSum 110 massAt 110 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed110 : packedAt 111 = (1 + digitBase) * nestedSum 110 packedAt 110 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign110 : SignCertificate 110 := by decide +kernel
private theorem checked110 : IndexCertificate 110 := ⟨mass110, packed110, fun _ => sign110⟩

private theorem mass111 : massAt 112 = 2 * nestedSum 111 massAt 111 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed111 : packedAt 112 = (1 + digitBase) * nestedSum 111 packedAt 111 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign111 : SignCertificate 111 := by decide +kernel
private theorem checked111 : IndexCertificate 111 := ⟨mass111, packed111, fun _ => sign111⟩

private theorem mass112 : massAt 113 = 2 * nestedSum 112 massAt 112 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed112 : packedAt 113 = (1 + digitBase) * nestedSum 112 packedAt 112 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign112 : SignCertificate 112 := by decide +kernel
private theorem checked112 : IndexCertificate 112 := ⟨mass112, packed112, fun _ => sign112⟩

private theorem mass113 : massAt 114 = 2 * nestedSum 113 massAt 113 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed113 : packedAt 114 = (1 + digitBase) * nestedSum 113 packedAt 113 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign113 : SignCertificate 113 := by decide +kernel
private theorem checked113 : IndexCertificate 113 := ⟨mass113, packed113, fun _ => sign113⟩

private theorem mass114 : massAt 115 = 2 * nestedSum 114 massAt 114 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed114 : packedAt 115 = (1 + digitBase) * nestedSum 114 packedAt 114 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign114 : SignCertificate 114 := by decide +kernel
private theorem checked114 : IndexCertificate 114 := ⟨mass114, packed114, fun _ => sign114⟩

private theorem mass115 : massAt 116 = 2 * nestedSum 115 massAt 115 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed115 : packedAt 116 = (1 + digitBase) * nestedSum 115 packedAt 115 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign115 : SignCertificate 115 := by decide +kernel
private theorem checked115 : IndexCertificate 115 := ⟨mass115, packed115, fun _ => sign115⟩

private theorem mass116 : massAt 117 = 2 * nestedSum 116 massAt 116 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed116 : packedAt 117 = (1 + digitBase) * nestedSum 116 packedAt 116 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign116 : SignCertificate 116 := by decide +kernel
private theorem checked116 : IndexCertificate 116 := ⟨mass116, packed116, fun _ => sign116⟩

private theorem mass117 : massAt 118 = 2 * nestedSum 117 massAt 117 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed117 : packedAt 118 = (1 + digitBase) * nestedSum 117 packedAt 117 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign117 : SignCertificate 117 := by decide +kernel
private theorem checked117 : IndexCertificate 117 := ⟨mass117, packed117, fun _ => sign117⟩

private theorem mass118 : massAt 119 = 2 * nestedSum 118 massAt 118 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed118 : packedAt 119 = (1 + digitBase) * nestedSum 118 packedAt 118 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign118 : SignCertificate 118 := by decide +kernel
private theorem checked118 : IndexCertificate 118 := ⟨mass118, packed118, fun _ => sign118⟩

private theorem mass119 : massAt 120 = 2 * nestedSum 119 massAt 119 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed119 : packedAt 120 = (1 + digitBase) * nestedSum 119 packedAt 119 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign119 : SignCertificate 119 := by decide +kernel
private theorem checked119 : IndexCertificate 119 := ⟨mass119, packed119, fun _ => sign119⟩

theorem certificates096To119 (n : ℕ) (hn : 96 ≤ n) (hn' : n ≤ 119) : IndexCertificate n := by
  interval_cases n
  · exact checked96
  · exact checked97
  · exact checked98
  · exact checked99
  · exact checked100
  · exact checked101
  · exact checked102
  · exact checked103
  · exact checked104
  · exact checked105
  · exact checked106
  · exact checked107
  · exact checked108
  · exact checked109
  · exact checked110
  · exact checked111
  · exact checked112
  · exact checked113
  · exact checked114
  · exact checked115
  · exact checked116
  · exact checked117
  · exact checked118
  · exact checked119

end PlanePartition
