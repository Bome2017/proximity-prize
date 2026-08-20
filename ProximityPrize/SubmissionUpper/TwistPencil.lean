import ProximityPrize.SubmissionUpper.TwistValueSpread

namespace ProximityPrize.SubmissionUpper

open ProximityPrize.Benchmark
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def diagWord (f : IRSProfile.Index → IRSProfile.Field) :
    IRSProfile.Index → Fin 8 → IRSProfile.Field := fun x _ => f x

structure PencilData where
  f₁ f₂ : IRSProfile.Index → IRSProfile.Field
  T : Finset IRSProfile.Field
  card_T : 2 ^ 58 ≤ T.card
  close_fold : ∀ γ ∈ T, ∃ q : Polynomial IRSProfile.Field,
    q.natDegree < 131072 ∧ ∃ S : Finset IRSProfile.Index,
      139502 ≤ S.card ∧ ∀ x ∈ S,
        f₁ x + γ * f₂ x = q.eval (IRSProfile.domain x)
  f₂_shape : ∃ α : IRSProfile.Field,
    (∀ x, IRSProfile.domain x ≠ α) ∧
      f₂ = fun x => -((IRSProfile.domain x - α)⁻¹)

theorem pencil_data_exists : PencilData := by
  classical
  obtain ⟨w, Hs, hHscard, hdeg, hagree⟩ := twist_center_exists
  obtain ⟨α, hα, hTcard⟩ := twist_value_spread Hs hdeg hHscard
  have hsubne : ∀ x, IRSProfile.domain x - α ≠ 0 := by
    intro x hx
    exact hα x (sub_eq_zero.mp hx)
  let f₁ : IRSProfile.Index → IRSProfile.Field :=
    fun x => w x * (IRSProfile.domain x - α)⁻¹
  let f₂ : IRSProfile.Index → IRSProfile.Field :=
    fun x => -((IRSProfile.domain x - α)⁻¹)
  let T := Hs.image (fun H => H.eval α)
  refine ⟨f₁, f₂, T, hTcard, ?_, ⟨α, hα, rfl⟩⟩
  intro γ hγT
  rw [T, Finset.mem_image] at hγT
  obtain ⟨H, hHmem, hHval⟩ := hγT
  have hHdeg := hdeg H hHmem
  obtain ⟨S, hScard, hSagree⟩ := hagree H hHmem
  let q := (H - Polynomial.C γ) /ₘ (Polynomial.X - Polynomial.C α)
  have hroot : (H - Polynomial.C γ).IsRoot α := by
    simp [Polynomial.IsRoot, hHval]
  have hdiv : (Polynomial.X - Polynomial.C α) * q = H - Polynomial.C γ := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqdeg : q.natDegree < 131072 := by
    rw [q, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C α)]
    have hle : (H - Polynomial.C γ).natDegree ≤ H.natDegree := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      exact max_le le_rfl (Nat.zero_le _)
    exact (Nat.sub_le _ _).trans hle |>.trans_lt hHdeg
  refine ⟨q, hqdeg, S, hScard, ?_⟩
  intro x hx
  have hid := congrArg (Polynomial.eval (IRSProfile.domain x)) hdiv
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hid
  have hw := hSagree x hx
  have hn := hsubne x
  dsimp [f₁, f₂]
  have hfactor : w x * (IRSProfile.domain x - α)⁻¹ +
      γ * -((IRSProfile.domain x - α)⁻¹) =
      (w x - γ) * (IRSProfile.domain x - α)⁻¹ := by ring
  rw [hfactor, ← hw, hid.symm, mul_comm (IRSProfile.domain x - α),
    mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem pencil_f₂_not_joint (P : PencilData) (δ : ℝ≥0) (hδ : δ < 1 / 2) :
    ¬ Code.jointProximity (IRSProfile.code : Set _)
      (u := fun a => if a = 0 then diagWord P.f₁ else diagWord P.f₂) δ := by
  classical
  obtain ⟨α, hα, hf₂⟩ := P.f₂_shape
  rw [← Code.jointAgreement_iff_jointProximity]
  rintro ⟨S, hScard, v, hv⟩
  have hv1 := hv (1 : Fin 2)
  have hv1mem : v 1 ∈ IRSProfile.code := hv1.1
  have hcoord : (fun x => v 1 x 0) ∈ ReedSolomon.code IRSProfile.domain 131072 :=
    (mem_code_iff (v 1)).mp hv1mem 0
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcoord
  obtain ⟨q, hqdeg, hqeval⟩ := hcoord
  have hSbig : 131072 < S.card := by
    have hcardI : (Fintype.card IRSProfile.Index : ℝ) = 262144 := by norm_num
    have hd : ((1 - δ : ℝ≥0) : ℝ) > 1 / 2 := by
      rw [NNReal.coe_sub (le_trans hδ.le (by norm_num : (1 / 2 : ℝ≥0) ≤ 1))]
      push_cast at hδ ⊢
      linarith
    have hsreal : (131072 : ℝ) < S.card := by
      calc
        (131072 : ℝ) = (1 / 2 : ℝ) * 262144 := by norm_num
        _ < ((1 - δ : ℝ≥0) : ℝ) * 262144 := by gcongr
        _ ≤ S.card := by simpa [hcardI] using hScard
    exact_mod_cast hsreal
  let R : Polynomial IRSProfile.Field :=
    (Polynomial.X - Polynomial.C α) * q + 1
  have hRzero : ∀ y ∈ S.image IRSProfile.domain, Polynomial.eval y R = 0 := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxS, rfl⟩ := hy
    have hag := Finset.mem_filter.mp (hv1.2 hxS) |>.2
    have hag0 := congrFun hag 0
    simp only [Fin.isValue, if_false, diagWord] at hag0
    rw [hf₂] at hag0
    have hq : q.eval (IRSProfile.domain x) = -((IRSProfile.domain x - α)⁻¹) := by
      rw [hqeval x, hag0]
    simp [R, hq, hα x]
  have hRdeg : R.natDegree ≤ 131072 := by
    dsimp [R]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_one, max_eq_left (Nat.zero_le _)]
    exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_X_sub_C]
      omega)
  have himage : (S.image IRSProfile.domain).card = S.card :=
    Finset.card_image_of_injective _ IRSProfile.domain.injective
  have hzero : R = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R _ hRzero
    rw [himage]
    exact hRdeg.trans_lt hSbig
  have hmul : (Polynomial.X - Polynomial.C α) * q = -1 := by
    dsimp [R] at hzero
    linear_combination hzero
  have hqne : q ≠ 0 := by
    intro h
    simp [h] at hmul
  have hdegprod := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α) hqne
  rw [hmul, Polynomial.natDegree_neg, Polynomial.natDegree_one,
    Polynomial.natDegree_X_sub_C] at hdegprod
  omega

theorem pencil_epsCa_lower (δ : ℝ≥0)
    (hlo : (122642 / 262144 : ℝ≥0) ≤ δ) (hhi : δ < 1 / 2) :
    ((2 ^ 58 : ℕ) : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤
      ProximityGap.epsCa (F := IRSProfile.Field)
        (IRSProfile.code : Set _) δ δ := by
  classical
  let P := pencil_data_exists
  let u : Code.WordStack (Fin 8 → IRSProfile.Field) (Fin 2) IRSProfile.Index :=
    fun a => if a = 0 then diagWord P.f₁ else diagWord P.f₂
  have hnj := pencil_f₂_not_joint P δ hhi
  have hsubset : P.T ⊆ Finset.univ.filter (fun γ : IRSProfile.Field =>
      δᵣ(u 0 + γ • u 1, (IRSProfile.code : Set _)) ≤ δ) := by
    intro γ hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨q, hqdeg, S, hScard, hagree⟩ := P.close_fold γ hγ
    let cw : IRSProfile.Index → Fin 8 → IRSProfile.Field :=
      diagWord (fun x => q.eval (IRSProfile.domain x))
    have hcw : cw ∈ IRSProfile.code := by
      rw [mem_code_iff]
      intro b
      rw [ReedSolomon.mem_code_iff_exists_polynomial]
      exact ⟨q, hqdeg, fun x => rfl⟩
    have hpair : δᵣ(u 0 + γ • u 1, cw) ≤ δ := by
      rw [Code.relCloseToWord_iff_exists_agreementCols]
      refine ⟨S, ?_, ?_⟩
      · rw [Code.relDist_floor_bound_iff_complement_bound]
        have hbase : (1 - δ) * (Fintype.card IRSProfile.Index : ℝ≥0) ≤ 139502 := by
          have hcard : (Fintype.card IRSProfile.Index : ℝ≥0) = 262144 := by norm_num
          rw [hcard]
          calc
            (1 - δ) * 262144 ≤ (1 - (122642 / 262144 : ℝ≥0)) * 262144 := by
              gcongr
            _ = 139502 := by norm_num
        exact hbase.trans (by exact_mod_cast hScard)
      · intro x
        constructor
        · intro hx
          have ha := hagree x hx
          funext b
          simpa [u, diagWord] using ha
        · intro hne hx
          exact hne ((by
            funext b
            simpa [u, diagWord] using hagree x hx) : (u 0 + γ • u 1) x = cw x)
    exact (Code.relDistFromCode_le_relDist_to_mem _ cw hcw).trans hpair
  unfold ProximityGap.epsCa
  refine le_trans ?_ (le_iSup (fun w : Code.WordStack (Fin 8 → IRSProfile.Field)
      (Fin 2) IRSProfile.Index => if Code.jointProximity (IRSProfile.code : Set _) w δ
        then 0 else Pr_{let γ ← $ᵖ IRSProfile.Field}[
          δᵣ(w 0 + γ • w 1, (IRSProfile.code : Set _)) ≤ δ]) u)
  rw [if_neg hnj, Probability.prob_uniform_eq_card_filter_div_card]
  rw [show ((Fintype.card IRSProfile.Field : ℝ≥0) : ENNReal) =
      (Fintype.card IRSProfile.Field : ENNReal) by rw [ENNReal.coe_natCast]]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast P.card_T.trans (Finset.card_le_card hsubset)

end ProximityPrize.SubmissionUpper
