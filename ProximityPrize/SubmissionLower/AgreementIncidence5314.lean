import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.AgreementIncidence5314

open scoped BigOperators
open ProximityPrize.Benchmark

variable {Seed Index : Type*}

/-- The number of selected seeds whose agreement support contains a coordinate. -/
def incidence [DecidableEq Seed] [DecidableEq Index] (seeds : Finset Seed)
    (support : Seed → Finset Index) (i : Index) : ℕ :=
  (seeds.filter fun s => i ∈ support s).card

/-- Coordinates occurring in more than `threshold` selected agreement supports. -/
def richCoordinates [Fintype Index] [DecidableEq Index] [DecidableEq Seed]
    (seeds : Finset Seed) (support : Seed → Finset Index) (threshold : ℕ) :
    Finset Index :=
  Finset.univ.filter fun i => threshold < incidence seeds support i

theorem incidence_le_card [DecidableEq Seed] [DecidableEq Index]
    (seeds : Finset Seed)
    (support : Seed → Finset Index) (i : Index) :
    incidence seeds support i ≤ seeds.card := by
  exact Finset.card_filter_le _ _

/-- Double-counting identity for the seed-coordinate incidence relation. -/
theorem sum_support_card_eq_sum_incidence [Fintype Index] [DecidableEq Index]
    [DecidableEq Seed] (seeds : Finset Seed) (support : Seed → Finset Index) :
    ∑ s ∈ seeds, (support s).card =
      ∑ i : Index, incidence seeds support i := by
  classical
  calc
    ∑ s ∈ seeds, (support s).card =
        ∑ s ∈ seeds, ∑ i : Index, if i ∈ support s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp
    _ = ∑ i : Index, ∑ s ∈ seeds,
          if i ∈ support s then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Index, incidence seeds support i := by
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ s ∈ seeds, if i ∈ support s then 1 else 0) =
        (seeds.filter fun s => i ∈ support s).card
      induction seeds using Finset.induction_on with
      | empty => simp
      | @insert a seeds ha ih =>
          by_cases hai : i ∈ support a
          · simp [ha, hai, ih]
          · simp [ha, hai, ih]

/-- If every seed agrees on at least `g` coordinates and the displayed
incidence inequality holds, then more than `k` coordinates are rich.  The
slightly loose `card(Index) * threshold` term keeps the statement easy to
reuse in the final extraction argument. -/
theorem card_richCoordinates_gt [Fintype Index] [DecidableEq Index]
    [DecidableEq Seed] (seeds : Finset Seed) (support : Seed → Finset Index)
    (g k threshold : ℕ)
    (hsupport : ∀ s ∈ seeds, g ≤ (support s).card)
    (hcount : k * seeds.card + Fintype.card Index * threshold <
      g * seeds.card) :
    k < (richCoordinates seeds support threshold).card := by
  classical
  by_contra hnot
  have hrich : (richCoordinates seeds support threshold).card ≤ k :=
    Nat.le_of_not_gt hnot
  have hlower : g * seeds.card ≤ ∑ s ∈ seeds, (support s).card := by
    calc
      g * seeds.card = ∑ _s ∈ seeds, g := by simp [Nat.mul_comm]
      _ ≤ ∑ s ∈ seeds, (support s).card :=
        Finset.sum_le_sum fun s hs => hsupport s hs
  have hpoint : ∀ i : Index,
      incidence seeds support i ≤
        (if i ∈ richCoordinates seeds support threshold then seeds.card else 0) +
          threshold := by
    intro i
    by_cases hi : i ∈ richCoordinates seeds support threshold
    · simp only [hi, if_true]
      exact (incidence_le_card seeds support i).trans (Nat.le_add_right _ _)
    · simp only [hi, if_false, zero_add]
      simpa [richCoordinates, incidence] using hi
  have hupper : (∑ i : Index, incidence seeds support i) ≤
      k * seeds.card + Fintype.card Index * threshold := by
    calc
      ∑ i : Index, incidence seeds support i ≤
          ∑ i : Index,
            ((if i ∈ richCoordinates seeds support threshold then seeds.card else 0) +
              threshold) := Finset.sum_le_sum fun i _ => hpoint i
      _ = (richCoordinates seeds support threshold).card * seeds.card +
            Fintype.card Index * threshold := by
          simp [Finset.sum_add_distrib]
      _ ≤ k * seeds.card + Fintype.card Index * threshold := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right seeds.card hrich) _
  rw [sum_support_card_eq_sum_incidence] at hlower
  exact (not_lt_of_ge (hlower.trans hupper)) hcount

/-- The concrete incidence budget used by the 53.14 extraction.  A branch of
more than `2^50` decoding polynomials has at least `k+1 = 131072`
coordinates occurring in more than `2^47` agreement supports.  This looser
but still valid threshold gives the algebraic resultant proof ample degree
budget. -/
theorem target5314_many_rich_coordinates [DecidableEq Seed]
    (seeds : Finset Seed) (support : Seed → Finset IRSProfile.Index)
    (hsupport : ∀ s ∈ seeds, 196592 ≤ (support s).card)
    (hseeds : 2 ^ 50 < seeds.card) :
    131071 < (richCoordinates seeds support (2 ^ 47)).card := by
  apply card_richCoordinates_gt seeds support 196592 131071 (2 ^ 47) hsupport
  have hindex : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  rw [hindex]
  nlinarith [show 2 ^ 50 < seeds.card from hseeds]

end ProximityPrize.SubmissionLower.AgreementIncidence5314
