import ProximityPrize.SubmissionLower.BCHKSStagedUnconditional6399
import ProximityPrize.SubmissionLower.BCHKSParameters

namespace ProximityPrize.SubmissionLower

/-- One-time bad-`Z` deletion for the 63.99 interpolation box. -/
theorem exists_bchks_Qbad_removal_6399
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (hS : bchksNumerator < S.card)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 13141403) :
    ∃ Sgood : Finset F,
      Sgood = S.filter (fun z => triSpecializeZ Q z ≠ 0) ∧
      Sgood ⊆ S ∧
      (∀ z ∈ Sgood, triSpecializeZ Q z ≠ 0) ∧
      (∀ z ∈ Sgood, triEval Q z (P z) = 0) ∧
      (S.filter (fun z => triSpecializeZ Q z = 0)).card ≤ 13141402 ∧
      632746 * (2 * 5279 * 13141402) +
          (76770 + 1) * 5279 + 2 * 13141403 * 5279 < Sgood.card := by
  classical
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hQ
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hj0
  have ha0 : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  have hdeg : ((Q.coeff j).coeff a).natDegree < 13141403 := by
    have := hQYZ j a ha0
    omega
  let Sgood := S.filter (fun z => triSpecializeZ Q z ≠ 0)
  have hbad : (badZSpecializations Q S).card ≤ 13141402 := by
    have hlt := badZSpecializations_card_lt Q S j a 13141403 ha0 hdeg
    omega
  have hbudget :
      632746 * (2 * 5279 * 13141402) +
          (76770 + 1) * 5279 + 2 * 13141403 * 5279 + 13141403 <
        bchksNumerator := by
    exact SecondStageCapacity.bchks_6399_raw_pair_capacity
  refine ⟨Sgood, rfl, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz
    exact hQeval z (Finset.mem_filter.mp hz).1
  · simpa [badZSpecializations] using hbad
  · have heq : Sgood = S \ badZSpecializations Q S := by
      ext z
      constructor
      · intro hz
        have hz' := Finset.mem_filter.mp hz
        exact Finset.mem_sdiff.mpr ⟨hz'.1, by
          simp [badZSpecializations, hz'.1, hz'.2]⟩
      · intro hz
        have hz' := Finset.mem_sdiff.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨hz'.1, ?_⟩
        intro hzero
        exact hz'.2 (by simp [badZSpecializations, hz'.1, hzero])
    rw [heq, Finset.card_sdiff]
    apply Nat.lt_sub_of_add_lt
    have hi : (badZSpecializations Q S ∩ S).card ≤ 13141402 :=
      (Finset.card_le_card Finset.inter_subset_left).trans hbad
    exact (Nat.add_le_add_left hi _).trans_lt
      ((by omega :
        632746 * (2 * 5279 * 13141402) +
            (76770 + 1) * 5279 + 2 * 13141403 * 5279 + 13141402 <
          bchksNumerator).trans hS)

end ProximityPrize.SubmissionLower
