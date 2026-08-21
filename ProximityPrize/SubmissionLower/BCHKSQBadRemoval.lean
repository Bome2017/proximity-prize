import ProximityPrize.SubmissionLower.BCHKSStagedArithmetic

namespace ProximityPrize.SubmissionLower

/-- Delete the points where the entire `Z`-specialization of the BCHKS
interpolant vanishes.  A single nonzero coefficient controls this deletion;
the interpolation `YZ` cap makes its size at most `55743` (and hence also the
coarser staged bound). -/
theorem exists_bchks_Qbad_removal
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (hS : bchksNumerator < S.card)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQY : Q.natDegree ≤ 282)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 55744)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 36923454) :
    ∃ Sgood : Finset F,
      Sgood = S.filter (fun z => triSpecializeZ Q z ≠ 0) ∧
      Sgood ⊆ S ∧
      (∀ z ∈ Sgood, triSpecializeZ Q z ≠ 0) ∧
      (∀ z ∈ Sgood, triEval Q z (P z) = 0) ∧
      (S.filter (fun z => triSpecializeZ Q z = 0)).card ≤
        2 * 55744 * 282 ∧
      bchksLinearCapacity * 282 + bchksNonlinearCapacity * 282 ^ 2 +
          (bchksErrors + 1) * 282 + 2 * 55744 * 282 < Sgood.card := by
  classical
  -- Keep the cap hypotheses in the interface used by the staged-pair theorem.
  clear hQY hQweightedX
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hQ
  have hj0 : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hj0
  have ha0 : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  have hdeg : ((Q.coeff j).coeff a).natDegree < 55744 := by
    have := hQYZ j a ha0
    omega
  let Sgood := S.filter (fun z => triSpecializeZ Q z ≠ 0)
  have hbad : (badZSpecializations Q S).card ≤ 55743 := by
    have := badZSpecializations_card_lt Q S j a 55744 ha0 hdeg
    omega
  have hSstrict : bchksNumerator < S.card := hS
  have hcard := bchks_staged_after_badZSpecializations Q S j a ha0 hdeg hSstrict
  refine ⟨Sgood, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz
    exact hQeval z (Finset.mem_filter.mp hz).1
  · simpa [badZSpecializations] using
      hbad.trans (by norm_num : 55743 ≤ 2 * 55744 * 282)
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
    rw [heq]
    exact hcard

end ProximityPrize.SubmissionLower
