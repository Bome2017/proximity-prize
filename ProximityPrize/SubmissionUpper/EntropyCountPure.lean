import ProximityPrize.Benchmark.TargetUpper

namespace ProximityPrize.SubmissionUpper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

lemma choose_mul_choose_le (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun _ _ => Nat.zero_le _)
    (show ((i, j) : ℕ × ℕ) ∈ Finset.antidiagonal (i + j) from
      Finset.mem_antidiagonal.mpr rfl)

lemma list_prod_choose_le (l : List (ℕ × ℕ)) :
    (l.map (fun pr => pr.1.choose pr.2)).prod ≤
      ((l.map Prod.fst).sum).choose ((l.map Prod.snd).sum) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (Nat.mul_le_mul_left _ ih).trans (choose_mul_choose_le _ _ _ _)

def twistChunks : List (ℕ × ℕ) :=
  List.replicate 6 (32768, 17438) ++ [(32768, 17437), (32767, 17437)]

theorem count_twist_n18 :
    2 ^ 59 * 2130706433 ^ 8430 ≤ Nat.choose 262144 139502 := by
  have hchunk : 2 ^ 59 * 2130706433 ^ 8430 ≤
      (twistChunks.map (fun pr => pr.1.choose pr.2)).prod := by
    rw [Nat.choose_eq_fast_choose]
    decide
  have hcombine := list_prod_choose_le twistChunks
  have hsum1 : (twistChunks.map Prod.fst).sum = 262143 := by decide
  have hsum2 : (twistChunks.map Prod.snd).sum = 139502 := by decide
  rw [hsum1, hsum2] at hcombine
  exact hchunk.trans (hcombine.trans (Nat.choose_le_choose 139502 (by norm_num)))

end ProximityPrize.SubmissionUpper
