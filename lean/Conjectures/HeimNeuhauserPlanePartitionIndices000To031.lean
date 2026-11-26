import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 0 through 31. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem checked0 : IndexCertificate 0 := by decide +kernel

private theorem checked1 : IndexCertificate 1 := by decide +kernel

private theorem checked2 : IndexCertificate 2 := by decide +kernel

private theorem checked3 : IndexCertificate 3 := by decide +kernel

private theorem checked4 : IndexCertificate 4 := by decide +kernel

private theorem checked5 : IndexCertificate 5 := by decide +kernel

private theorem checked6 : IndexCertificate 6 := by decide +kernel

private theorem checked7 : IndexCertificate 7 := by decide +kernel

private theorem checked8 : IndexCertificate 8 := by decide +kernel

private theorem checked9 : IndexCertificate 9 := by decide +kernel

private theorem checked10 : IndexCertificate 10 := by decide +kernel

private theorem checked11 : IndexCertificate 11 := by decide +kernel

private theorem mass12 : massAt 13 = 2 * nestedSum 12 massAt 12 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed12 : packedAt 13 = (1 + digitBase) * nestedSum 12 packedAt 12 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign12 : SignCertificate 12 := by decide +kernel
private theorem checked12 : IndexCertificate 12 := ⟨mass12, packed12, fun _ => sign12⟩

private theorem mass13 : massAt 14 = 2 * nestedSum 13 massAt 13 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed13 : packedAt 14 = (1 + digitBase) * nestedSum 13 packedAt 13 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign13 : SignCertificate 13 := by decide +kernel
private theorem checked13 : IndexCertificate 13 := ⟨mass13, packed13, fun _ => sign13⟩

private theorem mass14 : massAt 15 = 2 * nestedSum 14 massAt 14 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed14 : packedAt 15 = (1 + digitBase) * nestedSum 14 packedAt 14 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign14 : SignCertificate 14 := by decide +kernel
private theorem checked14 : IndexCertificate 14 := ⟨mass14, packed14, fun _ => sign14⟩

private theorem mass15 : massAt 16 = 2 * nestedSum 15 massAt 15 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed15 : packedAt 16 = (1 + digitBase) * nestedSum 15 packedAt 15 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign15 : SignCertificate 15 := by decide +kernel
private theorem checked15 : IndexCertificate 15 := ⟨mass15, packed15, fun _ => sign15⟩

private theorem mass16 : massAt 17 = 2 * nestedSum 16 massAt 16 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed16 : packedAt 17 = (1 + digitBase) * nestedSum 16 packedAt 16 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign16 : SignCertificate 16 := by decide +kernel
private theorem checked16 : IndexCertificate 16 := ⟨mass16, packed16, fun _ => sign16⟩

private theorem mass17 : massAt 18 = 2 * nestedSum 17 massAt 17 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed17 : packedAt 18 = (1 + digitBase) * nestedSum 17 packedAt 17 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign17 : SignCertificate 17 := by decide +kernel
private theorem checked17 : IndexCertificate 17 := ⟨mass17, packed17, fun _ => sign17⟩

private theorem mass18 : massAt 19 = 2 * nestedSum 18 massAt 18 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed18 : packedAt 19 = (1 + digitBase) * nestedSum 18 packedAt 18 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign18 : SignCertificate 18 := by decide +kernel
private theorem checked18 : IndexCertificate 18 := ⟨mass18, packed18, fun _ => sign18⟩

private theorem mass19 : massAt 20 = 2 * nestedSum 19 massAt 19 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed19 : packedAt 20 = (1 + digitBase) * nestedSum 19 packedAt 19 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign19 : SignCertificate 19 := by decide +kernel
private theorem checked19 : IndexCertificate 19 := ⟨mass19, packed19, fun _ => sign19⟩

private theorem mass20 : massAt 21 = 2 * nestedSum 20 massAt 20 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed20 : packedAt 21 = (1 + digitBase) * nestedSum 20 packedAt 20 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign20 : SignCertificate 20 := by decide +kernel
private theorem checked20 : IndexCertificate 20 := ⟨mass20, packed20, fun _ => sign20⟩

private theorem mass21 : massAt 22 = 2 * nestedSum 21 massAt 21 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed21 : packedAt 22 = (1 + digitBase) * nestedSum 21 packedAt 21 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign21 : SignCertificate 21 := by decide +kernel
private theorem checked21 : IndexCertificate 21 := ⟨mass21, packed21, fun _ => sign21⟩

private theorem mass22 : massAt 23 = 2 * nestedSum 22 massAt 22 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed22 : packedAt 23 = (1 + digitBase) * nestedSum 22 packedAt 22 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign22 : SignCertificate 22 := by decide +kernel
private theorem checked22 : IndexCertificate 22 := ⟨mass22, packed22, fun _ => sign22⟩

private theorem mass23 : massAt 24 = 2 * nestedSum 23 massAt 23 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed23 : packedAt 24 = (1 + digitBase) * nestedSum 23 packedAt 23 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign23 : SignCertificate 23 := by decide +kernel
private theorem checked23 : IndexCertificate 23 := ⟨mass23, packed23, fun _ => sign23⟩

private theorem mass24 : massAt 25 = 2 * nestedSum 24 massAt 24 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed24 : packedAt 25 = (1 + digitBase) * nestedSum 24 packedAt 24 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign24 : SignCertificate 24 := by decide +kernel
private theorem checked24 : IndexCertificate 24 := ⟨mass24, packed24, fun _ => sign24⟩

private theorem mass25 : massAt 26 = 2 * nestedSum 25 massAt 25 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed25 : packedAt 26 = (1 + digitBase) * nestedSum 25 packedAt 25 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign25 : SignCertificate 25 := by decide +kernel
private theorem checked25 : IndexCertificate 25 := ⟨mass25, packed25, fun _ => sign25⟩

private theorem mass26 : massAt 27 = 2 * nestedSum 26 massAt 26 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed26 : packedAt 27 = (1 + digitBase) * nestedSum 26 packedAt 26 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign26 : SignCertificate 26 := by decide +kernel
private theorem checked26 : IndexCertificate 26 := ⟨mass26, packed26, fun _ => sign26⟩

private theorem mass27 : massAt 28 = 2 * nestedSum 27 massAt 27 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed27 : packedAt 28 = (1 + digitBase) * nestedSum 27 packedAt 27 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign27 : SignCertificate 27 := by decide +kernel
private theorem checked27 : IndexCertificate 27 := ⟨mass27, packed27, fun _ => sign27⟩

private theorem mass28 : massAt 29 = 2 * nestedSum 28 massAt 28 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed28 : packedAt 29 = (1 + digitBase) * nestedSum 28 packedAt 28 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign28 : SignCertificate 28 := by decide +kernel
private theorem checked28 : IndexCertificate 28 := ⟨mass28, packed28, fun _ => sign28⟩

private theorem mass29 : massAt 30 = 2 * nestedSum 29 massAt 29 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed29 : packedAt 30 = (1 + digitBase) * nestedSum 29 packedAt 29 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign29 : SignCertificate 29 := by decide +kernel
private theorem checked29 : IndexCertificate 29 := ⟨mass29, packed29, fun _ => sign29⟩

private theorem mass30 : massAt 31 = 2 * nestedSum 30 massAt 30 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed30 : packedAt 31 = (1 + digitBase) * nestedSum 30 packedAt 30 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign30 : SignCertificate 30 := by decide +kernel
private theorem checked30 : IndexCertificate 30 := ⟨mass30, packed30, fun _ => sign30⟩

private theorem mass31 : massAt 32 = 2 * nestedSum 31 massAt 31 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed31 : packedAt 32 = (1 + digitBase) * nestedSum 31 packedAt 31 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign31 : SignCertificate 31 := by decide +kernel
private theorem checked31 : IndexCertificate 31 := ⟨mass31, packed31, fun _ => sign31⟩

theorem certificates000To031 (n : ℕ) (hn' : n ≤ 31) : IndexCertificate n := by
  interval_cases n
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31

end PlanePartition
