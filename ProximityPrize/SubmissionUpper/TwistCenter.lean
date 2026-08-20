import ProximityPrize.SubmissionUpper.SubsetList
import ProximityPrize.SubmissionUpper.EntropyCountPure

namespace ProximityPrize.SubmissionUpper

open ProximityPrize.Benchmark

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def diffPoly (T0 T : Finset IRSProfile.Index) : Polynomial IRSProfile.Field :=
  QFp T0 - QFp T

lemma diffPoly_injective (T0 : Finset IRSProfile.Index) {T T' : Finset IRSProfile.Index}
    (h : diffPoly T0 T = diffPoly T0 T') : T = T' := by
  have hq : QFp T = QFp T' := by
    apply sub_left_inj.mp
    simpa [diffPoly] using h
  ext i
  rw [← eval_QFp_eq_zero_iff T i, ← eval_QFp_eq_zero_iff T' i, hq]

theorem twist_center_exists :
    ∃ (w : IRSProfile.Index → IRSProfile.Field)
      (Hs : Finset (Polynomial IRSProfile.Field)),
      2 ^ 59 ≤ Hs.card ∧
      (∀ H ∈ Hs, H.natDegree < 131072) ∧
      (∀ H ∈ Hs, ∃ S : Finset IRSProfile.Index,
        139502 ≤ S.card ∧ ∀ x ∈ S, H.eval (IRSProfile.domain x) = w x) := by
  classical
  obtain ⟨v, -, hcard⟩ := exists_fiber count_twist_n18
  set fiber := ((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).filter
    (fun T => coeffTup T = v) with hfiber
  have hfne : fiber.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hcard)
  obtain ⟨T0, hT0mem⟩ := hfne
  have hT0f := Finset.mem_filter.mp hT0mem
  have hT0card : T0.card = 139502 := (Finset.mem_powersetCard.mp hT0f.1).2
  refine ⟨powWord T0, fiber.image (diffPoly T0), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (fun _ _ _ _ h => diffPoly_injective T0 h)]
    exact hcard
  · intro H hH
    rw [Finset.mem_image] at hH
    obtain ⟨T, hTmem, rfl⟩ := hH
    have hTf := Finset.mem_filter.mp hTmem
    have hTcard : T.card = 139502 := (Finset.mem_powersetCard.mp hTf.1).2
    have hc : coeffTup T = coeffTup T0 := by rw [hTf.2, hT0f.2]
    exact Nat.lt_of_le_of_lt (QFp_sub_natDegree_le hTcard hT0card hc) (by norm_num)
  · intro H hH
    rw [Finset.mem_image] at hH
    obtain ⟨T, hTmem, rfl⟩ := hH
    have hTf := Finset.mem_filter.mp hTmem
    have hTcard : T.card = 139502 := (Finset.mem_powersetCard.mp hTf.1).2
    refine ⟨T, hTcard.ge, ?_⟩
    intro x hx
    simp only [diffPoly, Polynomial.eval_sub, powWord]
    rw [(eval_QFp_eq_zero_iff T x).mpr hx, sub_zero]

end ProximityPrize.SubmissionUpper
