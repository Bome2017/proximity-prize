import ProximityPrize.SubmissionUpper.TwistCenter

namespace ProximityPrize.SubmissionUpper

open Polynomial Finset
open ProximityPrize.Benchmark
open scoped BigOperators

/-- Number of collision pairs of `f` on `Hs ×ˢ Hs` equals the sum of squared fiber sizes over the
    image. -/
theorem collisions_eq_sum_sq_fibers' {κ : Type*} [DecidableEq κ]
    (Hs : Finset (Polynomial IRSProfile.Field)) (f : Polynomial IRSProfile.Field → κ) :
    ((Hs ×ˢ Hs).filter (fun p => f p.1 = f p.2)).card
      = ∑ v ∈ Hs.image f, (Hs.filter (fun a => f a = v)).card ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Polynomial IRSProfile.Field × Polynomial IRSProfile.Field => f p.1)
      (t := Hs.image f)
      (fun p hp => by
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
        exact mem_image_of_mem f hp.1.1)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [sq, ← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hfab⟩, hfa⟩
    exact ⟨⟨ha, hfa⟩, hb, by rw [← hfab]; exact hfa⟩
  · rintro ⟨⟨ha, hfa⟩, hb, hfb⟩
    exact ⟨⟨⟨ha, hb⟩, by rw [hfa, hfb]⟩, hfa⟩

/-- Sum of fiber sizes over the image equals `#Hs`. -/
theorem sum_fibers_eq_card' {κ : Type*} [DecidableEq κ]
    (Hs : Finset (Polynomial IRSProfile.Field)) (f : Polynomial IRSProfile.Field → κ) :
    ∑ v ∈ Hs.image f, (Hs.filter (fun a => f a = v)).card = Hs.card := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Hs.image f) (fun a ha => mem_image_of_mem f ha)]

/-- **Cauchy–Schwarz image bound.**  `(#Hs)² ≤ #(image f) · coll`, where `coll` counts collision
    pairs on `Hs ×ˢ Hs`.  A small collision count forces a large image. -/
theorem card_sq_le_image_mul_collisions' {κ : Type*} [DecidableEq κ]
    (Hs : Finset (Polynomial IRSProfile.Field)) (f : Polynomial IRSProfile.Field → κ) :
    Hs.card ^ 2 ≤ (Hs.image f).card *
      ((Hs ×ˢ Hs).filter (fun p => f p.1 = f p.2)).card := by
  classical
  have hcs : (∑ v ∈ Hs.image f, ((Hs.filter (fun a => f a = v)).card : ℝ)) ^ 2
      ≤ ((Hs.image f).card : ℝ)
        * ∑ v ∈ Hs.image f, ((Hs.filter (fun a => f a = v)).card : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have e1 : (∑ v ∈ Hs.image f, ((Hs.filter (fun a => f a = v)).card : ℝ))
      = (Hs.card : ℝ) := by rw [← Nat.cast_sum, sum_fibers_eq_card' Hs f]
  have e2 : (∑ v ∈ Hs.image f, ((Hs.filter (fun a => f a = v)).card : ℝ) ^ 2)
      = (((Hs ×ˢ Hs).filter (fun p => f p.1 = f p.2)).card : ℝ) := by
    rw [collisions_eq_sum_sq_fibers' Hs f]; push_cast; ring
  rw [e1, e2] at hcs
  exact_mod_cast hcs

/-- The collision count splits into off-diagonal collisions plus the diagonal (of size `#Hs`). -/
theorem collisions_split {κ : Type*} [DecidableEq κ]
    (Hs : Finset (Polynomial IRSProfile.Field)) (f : Polynomial IRSProfile.Field → κ) :
    ((Hs ×ˢ Hs).filter (fun p => f p.1 = f p.2)).card
      = ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)).card + Hs.card := by
  classical
  have hdiag : ((Hs ×ˢ Hs).filter (fun p => p.1 = p.2 ∧ f p.1 = f p.2)).card = Hs.card := by
    rw [← Finset.card_image_of_injective Hs (f := fun a => (a, a)) (by intro a b h; simpa using h)]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab, _⟩; subst hab; exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨c, hc, h1, h2⟩; subst h1; subst h2; exact ⟨⟨hc, hc⟩, rfl, rfl⟩
  rw [add_comm, ← hdiag, ← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    by_cases hab : a = b <;> simp [hab]
  · rw [Finset.disjoint_filter]
    rintro ⟨a, b⟩ _ ⟨hab, _⟩ ⟨hne, _⟩
    exact hne hab

/-- **Per-pair agreement bound.**  Distinct deg-`< 2²⁰` polynomials agree at `≤ 2²⁰ − 1` points of
    any `G : Finset IRSProfile.Field` (root count of their difference). -/
theorem agree_card_le (G : Finset IRSProfile.Field) (H1 H2 : Polynomial IRSProfile.Field)
    (hne : H1 ≠ H2) (hd1 : H1.natDegree < 131072) (hd2 : H2.natDegree < 131072) :
    (G.filter (fun α => H1.eval α = H2.eval α)).card ≤ 131072 - 1 := by
  classical
  set D := H1 - H2 with hD
  have hDne : D ≠ 0 := sub_ne_zero.mpr hne
  have hDdeg : D.natDegree < 131072 :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (by simp only [max_lt_iff]; exact ⟨hd1, hd2⟩)
  have hsub : (G.filter (fun α => H1.eval α = H2.eval α)) ⊆ D.roots.toFinset := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hDne, Polynomial.IsRoot.def, hD,
      Polynomial.eval_sub, sub_eq_zero]
    exact hα.2
  calc (G.filter (fun α => H1.eval α = H2.eval α)).card
      ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := D.card_roots'
    _ ≤ 131072 - 1 := by omega

/-- **Double counting.**  Summing the off-diagonal collision counts over `G` is at most
    `(#Hs)² · (2²⁰ − 1)`: swap the order and use the per-pair agreement bound. -/
theorem sum_collD_le (G : Finset IRSProfile.Field) (Hs : Finset (Polynomial IRSProfile.Field))
    (hdeg : ∀ H ∈ Hs, H.natDegree < 131072) :
    ∑ α ∈ G, ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card
      ≤ Hs.card * Hs.card * (131072 - 1) := by
  classical
  have step1 : ∀ α ∈ G,
      ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card
        = ∑ p ∈ Hs ×ˢ Hs, (if p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α then 1 else 0) := by
    intro α _; rw [Finset.card_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∑ p ∈ Hs ×ˢ Hs, ∑ α ∈ G,
      (if p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α then 1 else 0)
        ≤ ∑ p ∈ Hs ×ˢ Hs, (131072 - 1) := by
    apply Finset.sum_le_sum
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    by_cases hab : a = b
    · simp [hab]
    · have hrw : ∑ α ∈ G, (if a ≠ b ∧ a.eval α = b.eval α then 1 else 0)
          = (G.filter (fun α => a.eval α = b.eval α)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun α _ => by simp [hab])
      rw [hrw]
      exact agree_card_le G a b hab (hdeg a hp.1) (hdeg b hp.2)
  refine le_trans step2 ?_
  rw [Finset.sum_const, Finset.card_product, smul_eq_mul]

/-- **Twist value spread (BCHKS Lemma 6.1).**  A family of `≥ 2⁵⁹` polynomials of natDegree
    `< 2²⁰` takes `≥ 2⁵⁸` distinct values at some challenge `α` off the domain. -/
theorem twist_value_spread (Hs : Finset (Polynomial IRSProfile.Field))
    (hdeg : ∀ H ∈ Hs, H.natDegree < 131072) (hcard : 2 ^ 59 ≤ Hs.card) :
    ∃ α : IRSProfile.Field, (∀ x : IRSProfile.Index, IRSProfile.domain x ≠ α) ∧
      2 ^ 58 ≤ (Hs.image (fun H => H.eval α)).card := by
  classical
  set L := Hs.card with hLdef
  set G : Finset IRSProfile.Field := Finset.univ \ (Finset.univ.image IRSProfile.domain) with hGdef
  -- |G| ≥ 2^179
  have hGcard : (2 : ℕ) ^ 179 ≤ G.card := by
    rw [hGdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_image_of_injective _ IRSProfile.domain.injective, KoalaBear.card_ext6]
    have hp : (2 : ℕ) ^ 30 ≤ 2130706433 := by norm_num [2130706433]
    have hp6 : (2 : ℕ) ^ 180 ≤ 2130706433 ^ 6 := by
      calc (2 : ℕ) ^ 180 = (2 ^ 30) ^ 6 := by norm_num
        _ ≤ 2130706433 ^ 6 := Nat.pow_le_pow_left hp 6
    omega
  -- Suppose for contradiction every α ∈ G has image ≤ 2^58 − 1.
  by_contra hcon
  push Not at hcon
  -- from hcon: for every α off the domain, image < 2^58; specialize to α ∈ G
  have hsmall : ∀ α ∈ G, (Hs.image (fun H => H.eval α)).card ≤ 2 ^ 58 - 1 := by
    intro α hαG
    have hαdom : α ∉ (Finset.univ.image IRSProfile.domain) := (Finset.mem_sdiff.mp (by rw [← hGdef]; exact hαG)).2
    have havoid : ∀ x : IRSProfile.Index, IRSProfile.domain x ≠ α := by
      intro x hx; exact hαdom (by rw [← hx]; exact Finset.mem_image_of_mem IRSProfile.domain (Finset.mem_univ x))
    have := hcon α havoid
    omega
  -- per-α: 2 * ((2^58 − 1) * collD(α)) ≥ L² for α ∈ G
  have hperα : ∀ α ∈ G,
      2 * ((2 ^ 58 - 1) *
        ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card) ≥ L ^ 2 := by
    intro α hαG
    set collD := ((Hs ×ˢ Hs).filter
      (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card with hcollD
    have hCS : L ^ 2 ≤ (Hs.image (fun H => H.eval α)).card * (collD + L) := by
      have key := card_sq_le_image_mul_collisions' Hs (fun H => H.eval α)
      have hsplit := collisions_split Hs (fun H => H.eval α)
      rw [hsplit] at key
      simpa [hLdef, hcollD] using key
    have himg : (Hs.image (fun H => H.eval α)).card ≤ 2 ^ 58 - 1 := hsmall α hαG
    have hcs : (2 ^ 58 - 1) * (collD + L) ≥ L ^ 2 := by
      refine le_trans hCS ?_
      exact Nat.mul_le_mul_right _ himg
    have hexp : (2 ^ 58 - 1) * collD + (2 ^ 58 - 1) * L ≥ L ^ 2 := by
      rw [← Nat.mul_add]; exact hcs
    have hL : (2 : ℕ) ^ 59 ≤ L := hcard
    have hbig : 2 * ((2 ^ 58 - 1) * L) ≤ L * L := by
      have h2 : 2 * (2 ^ 58 - 1) ≤ L := by omega
      calc 2 * ((2 ^ 58 - 1) * L) = (2 * (2 ^ 58 - 1)) * L := by ring
        _ ≤ L * L := Nat.mul_le_mul_right _ h2
    have hLL : L ^ 2 = L * L := sq L
    nlinarith [hexp, hbig, hLL]
  -- Sum the per-α bound over G.
  set SigmaCollD := ∑ α ∈ G,
    ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card with hSig
  have hlow : 2 * ((2 ^ 58 - 1) * SigmaCollD) ≥ G.card * L ^ 2 := by
    rw [hSig, Finset.mul_sum, Finset.mul_sum]
    calc G.card * L ^ 2 = ∑ _α ∈ G, L ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ α ∈ G, 2 * ((2 ^ 58 - 1) *
          ((Hs ×ˢ Hs).filter (fun p => p.1 ≠ p.2 ∧ p.1.eval α = p.2.eval α)).card) :=
        Finset.sum_le_sum hperα
  have hhigh : (2 ^ 58 - 1) * SigmaCollD ≤ 2 ^ 58 * (L ^ 2 * 131072) := by
    have hdc := sum_collD_le G Hs hdeg
    rw [← hSig] at hdc
    calc (2 ^ 58 - 1) * SigmaCollD ≤ 2 ^ 58 * SigmaCollD := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ 58 * (L * L * (131072 - 1)) := Nat.mul_le_mul_left _ hdc
      _ ≤ 2 ^ 58 * (L ^ 2 * 131072) := by
          apply Nat.mul_le_mul_left
          rw [sq]
          exact Nat.mul_le_mul_left _ (by omega)
  -- Final contradiction.
  have hpos : 0 < L ^ 2 := by
    have : 0 < L := by have : (2 : ℕ) ^ 59 ≤ L := hcard; omega
    positivity
  have step : 2 * (2 ^ 58 * (L ^ 2 * 131072)) ≥ G.card * L ^ 2 := by
    calc G.card * L ^ 2 ≤ 2 * ((2 ^ 58 - 1) * SigmaCollD) := hlow
      _ ≤ 2 * (2 ^ 58 * (L ^ 2 * 131072)) := by omega
  have hGmul : 2 ^ 179 * L ^ 2 ≤ G.card * L ^ 2 := Nat.mul_le_mul_right _ hGcard
  have hchain : 2 ^ 179 * L ^ 2 ≤ 2 * (2 ^ 58 * (L ^ 2 * 131072)) := le_trans hGmul step
  nlinarith [hchain, hpos]

end ProximityPrize.Squeeze.MCAAttack
