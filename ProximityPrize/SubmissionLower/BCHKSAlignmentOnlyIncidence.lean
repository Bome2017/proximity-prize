import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Coordinate-incidence extraction under the alignment-only seed budget. -/
theorem exists_large_domain_fibers_alignment_only
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : T → Polynomial IRSProfile.Field)
    (dH d D : ℕ)
    (hrow : ∀ z ∈ T, 262144 - 76717 ≤ (A z).card)
    (hT : 634000 * D * dH * d + 76717 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + (z : IRSProfile.Field) * U 1 i) :
    ∃ A' : Finset IRSProfile.Field, 131072 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 131071 + 2) * dH * d * D < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : IRSProfile.Index,
          IRSProfile.domain i = (x : IRSProfile.Field) ∧
          Polynomial.eval (x : IRSProfile.Field) (P z) =
            U 0 i + (z : IRSProfile.Field) * U 1 i := by
  classical
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 131071 + 2) * dH * d * D <
      (T.filter fun z => i ∈ A z).card
  have hG : 131072 ≤ G.card := by
    simpa [G] using concrete_many_large_fibers_alignment_only T A dH d D
      (by norm_num [IRSProfile.Index]) hrow hT
  let A' : Finset IRSProfile.Field := G.image IRSProfile.domain
  have hA' : A'.card = G.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
  let idx : A' → IRSProfile.Index := fun x => Classical.choose
    (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧
      IRSProfile.domain (idx x) = (x : IRSProfile.Field) := by
    exact Classical.choose_spec (Finset.mem_image.mp x.property)
  let Fib : A' → Finset T := fun x => T.attach.filter fun z =>
    idx x ∈ A (z : IRSProfile.Field)
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 131071 + 2) * dH * d * D <
      (T.attach.filter (fun z : T => idx x ∈ A (z : IRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : IRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : IRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA

end ProximityPrize.SubmissionLower
