import Conjectures.HeimNeuhauserPlanePartitionData

/-! A kernel-friendly form of the nested recurrence sum.

Kernel reduction of `nestedSum n massAt n` near `n = 250` costs about a gigabyte of
memory. Most of it comes from the `Finset` sums over `Nat.divisors` in
`divisorSquareSum` and from the indexed lookups `massData[i]?`. Together they exceed
the `-M4500` cap of `lake build` on Linux runners. `foldRows` computes the same number in
one pass over the stored rows, with the divisor sums by plain `Nat.rec`.
`nestedSum_massAt` and `nestedSum_packedAt` let each certificate rewrite to that form
before `decide +kernel`. The certificate statements are unchanged. -/

namespace PlanePartition

open Finset

/-- `divisorSquareSumAux k m` is the sum of `d ^ 2` over the divisors `d ≤ m` of `k`. -/
noncomputable def divisorSquareSumAux (k m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun d s => s + if k % (d + 1) = 0 then (d + 1) * (d + 1) else 0) m

private theorem sum_filter_eq_aux (k m : ℕ) :
    ∑ d ∈ (Ico 1 (m + 1)).filter (· ∣ k), d ^ 2 = divisorSquareSumAux k m := by
  rw [Finset.sum_filter]
  induction m with
  | zero => simp [divisorSquareSumAux]
  | succ m ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, sq]
    change _ = divisorSquareSumAux k m + _
    simp only [Nat.dvd_iff_mod_eq_zero]

theorem divisorSquareSum_eq_aux (k : ℕ) : divisorSquareSum k = divisorSquareSumAux k k :=
  sum_filter_eq_aux k k

/-- One pass of the nested recurrence over the stored rows `rs`, starting at index `i`. -/
noncomputable def foldRows (n : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | _, acc, [] => acc
  | i, acc, r :: rs => foldRows n (i + 1) (divisorSquareSumAux (n + 1 - i) (n + 1 - i) * r + i * acc) rs

private theorem nestedSum_eq_foldl (n : ℕ) (row : ℕ → ℕ) (m : ℕ) :
    nestedSum n row m = (List.range (m + 1)).foldl
      (fun a t => divisorSquareSum (n + 1 - t) * row t + t * a) 0 := by
  induction m with
  | zero => simp [nestedSum]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ← ih, nestedSum]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_add_right]

private theorem foldRows_eq (n : ℕ) (row : ℕ → ℕ) :
    ∀ (rs : List ℕ) (i acc : ℕ), (∀ j (h : j < rs.length), rs[j] = row (i + j)) →
      foldRows n i acc rs = (List.range' i rs.length).foldl
        (fun a t => divisorSquareSum (n + 1 - t) * row t + t * a) acc
  | [], _, _, _ => by simp [foldRows]
  | r :: rs, i, acc, h => by
    have hr : r = row i := h 0 (by simp)
    rw [foldRows, List.length_cons, List.range'_succ, List.foldl_cons, hr,
      divisorSquareSum_eq_aux]
    refine foldRows_eq n row rs (i + 1) _ fun j hj => ?_
    rw [show i + 1 + j = i + (j + 1) by omega]
    exact h (j + 1) (Nat.succ_lt_succ hj)

theorem nestedSum_data (data : Array ℕ) (n m : ℕ) (hm : m < data.size) :
    nestedSum n (fun i => data[i]?.getD 0) m = foldRows n 0 0 (data.toList.take (m + 1)) := by
  have hlen : (data.toList.take (m + 1)).length = m + 1 := by simp; omega
  rw [nestedSum_eq_foldl, foldRows_eq n _ _ 0 0, hlen, List.range_eq_range']
  intro j hj
  rw [hlen] at hj
  simp [List.getElem_take, Array.getElem?_eq_getElem (by omega : j < data.size)]

theorem massData_size : massData.size = 252 := by decide +kernel

theorem packedData_size : packedData.size = 252 := by decide +kernel

theorem nestedSum_massAt (n m : ℕ) (hm : m ≤ 250) :
    nestedSum n massAt m = foldRows n 0 0 (massData.toList.take (m + 1)) :=
  nestedSum_data massData n m (by rw [massData_size]; omega)

theorem nestedSum_packedAt (n m : ℕ) (hm : m ≤ 250) :
    nestedSum n packedAt m = foldRows n 0 0 (packedData.toList.take (m + 1)) :=
  nestedSum_data packedData n m (by rw [packedData_size]; omega)

end PlanePartition
