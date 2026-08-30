import ProximityPrize.SubmissionLower.RFreeBasisOrders
import ProximityPrize.SubmissionLower.Q4
import ProximityPrize.SubmissionLower.BS
import ProximityPrize.SubmissionLower.BD
import ProximityPrize.SubmissionLower.AD

namespace ProximityPrize.SubmissionLower.RFreeDerivativeCertificate

open scoped BigOperators
open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research
open ContactFlagRankKernel6641Research ContactKernelCommonGCDResearch
open ContactKernelGenericChoiceResearch
open ContactKernelSelectedInterpolation6733Research
open ContactFlagTranslation6641Research
open ContactImplicitContactLift ContactRegularFactorGate
open ContactGCDCumulativeFlagsResearch
open ContactPost6464MinkowskiRecurrenceResearch
open RFreeDerivativeTransport RFreeJetCodimension
open RFreeScaledJetBridge RFreeBasisOrders

noncomputable section

set_option maxHeartbeats 500000
set_option maxRecDepth 1000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev Field := IRSProfile.Field
abbrev Index := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) Field

def flagRfreeToOrdinary (D w L : ℕ) :
    ContactFlagInterpolation6641Research.globalCoefficientBox
        Field D w L 0 →ₗ[Field]
      ContactInterpolation.globalCoefficientBox Field D w L 0 where
  toFun Q := ⟨Q.1, by
    intro e he
    have hh := Q.2 he
    change e 1 + e 2 + e 3 ≤ L ∧ e 2 ≤ 0 ∧
      e 0 + w * e 1 + (w - 1) * e 2 < D at hh
    change e 1 + e 3 ≤ L ∧ e 2 ≤ 0 ∧
      e 0 + w * e 1 + (w - 1) * e 2 < D
    omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flagRfreeToOrdinary_injective (D w L : ℕ) :
    Function.Injective (flagRfreeToOrdinary D w L) := by
  intro Q R h
  apply Subtype.ext
  exact congrArg (fun T ↦ T.1) h

def ordinaryRfreeToFlag (D w L : ℕ) :
    ContactInterpolation.globalCoefficientBox Field D w L 0 →ₗ[Field]
      ContactFlagInterpolation6641Research.globalCoefficientBox
        Field D w L 0 where
  toFun Q := ⟨Q.1, by
    intro e he
    have hh := Q.2 he
    change e 1 + e 3 ≤ L ∧ e 2 ≤ 0 ∧
      e 0 + w * e 1 + (w - 1) * e 2 < D at hh
    change e 1 + e 2 + e 3 ≤ L ∧ e 2 ≤ 0 ∧
      e 0 + w * e 1 + (w - 1) * e 2 < D
    omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rfreeBoxEquiv (D w L : ℕ) :
    ContactFlagInterpolation6641Research.globalCoefficientBox
        Field D w L 0 ≃ₗ[Field]
    ContactInterpolation.globalCoefficientBox Field D w L 0 :=
  LinearEquiv.ofLinear (flagRfreeToOrdinary D w L)
    (ordinaryRfreeToFlag D w L)
    (by
      apply LinearMap.ext
      intro Q
      exact Subtype.ext rfl)
    (by
      apply LinearMap.ext
      intro Q
      exact Subtype.ext rfl)

private theorem rfree_coefficientCount_eq (D w L : ℕ) :
    ContactInterpolation.coefficientCount D w L 0 =
      ContactFlagInterpolation6641Research.coefficientCount D w L 0 := by
  simp [ContactInterpolation.coefficientCount,
    ContactFlagInterpolation6641Research.coefficientCount]

private theorem ordinary_rfree_finrank (D w L : ℕ) :
    Module.finrank Field
        (ContactInterpolation.globalCoefficientBox Field D w L 0) =
      ContactInterpolation.coefficientCount D w L 0 := by
  rw [rfree_coefficientCount_eq]
  rw [← ContactKernelCommonGCDResearch.globalCoefficientBox_finrank
    (K := Field) D w L 0]
  exact LinearEquiv.finrank_eq (rfreeBoxEquiv D w L).symm

def profileAContact {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) : ℕ :=
  wt (ContactFactorCaps.contactWeights 131071) S.G

def profileAComplement {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) : ℕ :=
  7645344 - profileAContact S

def profileAQuotientPolynomial {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) (v : AKernel u0 u1) : Poly4 :=
  Classical.choose (S.G_dvd_A v)

theorem profileA_factor {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) (v : AKernel u0 u1) :
    reconstruct Field 7645344 131071 84439 12 v.1 =
      S.G * profileAQuotientPolynomial S v :=
  Classical.choose_spec (S.G_dvd_A v)

def profileAQuotientLinear {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) : AKernel u0 u1 →ₗ[Field] Poly4 where
  toFun := profileAQuotientPolynomial S
  map_add' v z := by
    apply mul_left_cancel₀ S.G_ne
    rw [mul_add, ← profileA_factor S (v + z), ← profileA_factor S v,
      ← profileA_factor S z]
    classical
    simp [ContactFlagInterpolation6641Research.reconstruct,
      Finset.sum_add_distrib]
  map_smul' a v := by
    apply mul_left_cancel₀ S.G_ne
    rw [← profileA_factor S (a • v)]
    calc
      reconstruct Field 7645344 131071 84439 12 (a • v).1 =
          a • reconstruct Field 7645344 131071 84439 12 v.1 :=
        (by
          classical
          simp [ContactFlagInterpolation6641Research.reconstruct,
            Finset.smul_sum, MvPolynomial.smul_monomial, smul_eq_mul])
      _ = a • (S.G * profileAQuotientPolynomial S v) := by
        rw [profileA_factor S v]
      _ = S.G * (a • profileAQuotientPolynomial S v) := by
        simp only [MvPolynomial.smul_eq_C_mul]
        ac_rfl

theorem profileAQuotientLinear_injective {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) :
    Function.Injective (profileAQuotientLinear S) := by
  intro v z hvz
  have hq : profileAQuotientPolynomial S v =
      profileAQuotientPolynomial S z := hvz
  have hrecon : reconstruct Field 7645344 131071 84439 12 v.1 =
      reconstruct Field 7645344 131071 84439 12 z.1 := by
    rw [profileA_factor S v, profileA_factor S z, hq]
  exact Subtype.ext (reconstruct_injective Field
    7645344 131071 84439 12 hrecon)

theorem profileAQuotient_mem {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G)
    (v : AKernel u0 u1) :
    profileAQuotientPolynomial S v ∈
      globalCoefficientBox Field (profileAComplement S) 131071 84439 0 := by
  let R := profileAQuotientPolynomial S v
  by_cases hR : R = 0
  · simpa only [R, hR] using
      (show (0 : Poly4) ∈
          globalCoefficientBox Field (profileAComplement S) 131071 84439 0
        from Submodule.zero_mem _)
  · have hfactor := profileA_factor S v
    have hrecon : reconstruct Field 7645344 131071 84439 12 v.1 ≠ 0 := by
      rw [hfactor]
      exact mul_ne_zero S.G_ne hR
    have hbox : reconstruct Field 7645344 131071 84439 12 v.1 ∈
        globalCoefficientBox Field 7645344 131071 84439 12 := by
      exact reconstruct_mem_globalCoefficientBox Field _ _ _ _ v.1
    have hqbox := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (reconstruct Field 7645344 131071 84439 12 v.1) S.G R
      7645344 131071 84439 12
      (profileAContact S) 0 12 hrecon S.G_ne hR hbox hfactor le_rfl
      (Nat.zero_le _) hslope
    simpa only [R, profileAComplement, Nat.sub_zero] using hqbox

def profileAQuotientMap {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G) :
    AKernel u0 u1 →ₗ[Field]
      globalCoefficientBox Field (profileAComplement S) 131071 84439 0 :=
  LinearMap.codRestrict
    (globalCoefficientBox Field (profileAComplement S) 131071 84439 0)
    (profileAQuotientLinear S) (profileAQuotient_mem S hslope)

@[simp] theorem profileAQuotientMap_apply_val {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G)
    (v : AKernel u0 u1) :
    (profileAQuotientMap S hslope v).1 = profileAQuotientPolynomial S v := rfl

theorem profileAQuotientMap_injective {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G) :
    Function.Injective (profileAQuotientMap S hslope) := by
  intro v z hvz
  apply profileAQuotientLinear_injective S
  exact congrArg (fun Q : globalCoefficientBox Field
    (profileAComplement S) 131071 84439 0 ↦ Q.1) hvz

abbrev ProfileAQuotientRange {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G) :=
  LinearMap.range (profileAQuotientMap S hslope)

def extendIndexFunction (f : Index → Field) : Field → Field :=
  fun x ↦ f (Function.invFun IRSProfile.domain x)

def profileALocalOrder {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1)
    (hslope : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G)
    (x : Field) : ℕ :=
  cappedLocalOrder (profileAComplement S) 131071 84439
    (ProfileAQuotientRange S hslope) x
    (extendIndexFunction u0 x) (extendIndexFunction u1 x)

private theorem forty_one_mul_card_sub_sum_le_sum_sub
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℕ)
    (hf : ∀ i ∈ s, f i ≤ 42) :
    41 * s.card - ∑ i ∈ s, f i ≤ ∑ i ∈ s, (41 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, Finset.sum_insert hi,
        Finset.sum_insert hi]
      have hfi := hf i (Finset.mem_insert_self i s)
      have hrest : ∀ j ∈ s, f j ≤ 42 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hih := ih hrest
      omega

private theorem right_le_of_codimension_capacity
    {A B C cap : ℕ} (hB : B ≤ A) (hC : C ≤ A - B)
    (hcap : A - C ≤ cap) : B ≤ cap := by
  omega

set_option maxHeartbeats 1500000 in
theorem profileA_quotient_gap {u0 u1 : Index → Field}
    (S : SelectedInterpolants u0 u1) (support : Finset Index)
    (hcard : support.card = 182032)
    (hysLower : 54 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualYSWeights S.G)
    (hslopeLower : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G)
    (hslopeUpper : wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G ≤ 12) :
    50963 ≤ profileAComplement S -
      ∑ x ∈ support.map IRSProfile.domain,
        profileALocalOrder S hslopeLower x := by
  classical
  let d := profileAComplement S
  let W := ProfileAQuotientRange S hslopeLower
  let u0e := extendIndexFunction u0
  let u1e := extendIndexFunction u1
  let points := support.map IRSProfile.domain
  let h := profileALocalOrder S hslopeLower
  have hcUpper : profileAContact S ≤ 7645343 := by
    have hcaps := (mem_flagGlobalCoefficientBox_iff S.G
      7645344 131071 13754 12 (by norm_num)).mp S.G_flagC
    exact hcaps.2.2
  have hcLower : 7077822 ≤ profileAContact S := by
    exact ContactTwoTailResidualGeneric6734Research.gcd_contact_lower
      S.G 54 12 hysLower hslopeUpper
  have hdUpper : d ≤ 567522 := by
    dsimp only [d, profileAComplement]
    omega
  let qo : W →ₗ[Field]
      ContactInterpolation.globalCoefficientBox Field d 131071 84439 0 :=
    (flagRfreeToOrdinary d 131071 84439).comp W.subtype
  let Wo : Submodule Field
      (ContactInterpolation.globalCoefficientBox Field d 131071 84439 0) :=
    LinearMap.range qo
  letI : Module.Finite Field
      (ContactInterpolation.globalCoefficientBox Field d 131071 84439 0) :=
    Module.Finite.of_surjective (flagRfreeToOrdinary d 131071 84439)
      (rfreeBoxEquiv d 131071 84439).surjective
  have hpointsCard : points.card = 182032 := by
    dsimp only [points]
    rw [Finset.card_map, hcard]
  have hWfinrank : Module.finrank Field W =
      Module.finrank Field (AKernel u0 u1) := by
    exact LinearMap.finrank_range_of_inj
      (profileAQuotientMap_injective S hslopeLower)
  have hWLower :
      coefficientCount 7645344 131071 84439 12 -
          262144 * localRankBound 42 84439 12 ≤
        Module.finrank Field W := by
    rw [hWfinrank]
    have hlo := constraintKernel_finrank_lower_bound (K := Field)
      7645344 131071 84439 12 42 IRSProfile.domain u0 u1
    have hcardI : Fintype.card Index = 262144 := by
      norm_num [Index, IRSProfile.Index]
    simpa only [hcardI] using hlo
  have hWoFinrank : Module.finrank Field Wo = Module.finrank Field W := by
    apply LinearMap.finrank_range_of_inj
    intro Q R hQR
    apply Subtype.ext
    apply flagRfreeToOrdinary_injective d 131071 84439
    exact hQR
  have hWoker : Wo ≤ LinearMap.ker
      (rfreeSelectedJetMap d 131071 84439 points h u0e u1e) := by
    intro Q hQ
    obtain ⟨Qf, hQf⟩ := hQ
    apply mem_ker_rfreeSelectedJetMap_of_scaled_contact
    intro x
    have hdvd := scaledTranslation_dvd d 131071 84439 W
      (x : Field) (u0e x) (u1e x) Qf
    have hval := congrArg Subtype.val hQf
    change Qf.1 = Q.1 at hval
    rwa [← hval]
  by_contra hnot
  have hsmall : d - ∑ x ∈ points, h x ≤ 50962 := by
    dsimp only [d, points, h]
    omega
  have hcodim := rfree_profileA_five_channel_codimension_of_le
    d hdUpper points h u0e u1e Wo hWoker
  have hcapacity := profileA_five_channel_capacity
    d hdUpper points h hpointsCard hsmall
  have hAmbient := ordinary_rfree_finrank d 131071 84439
  have hWoLe := Wo.finrank_le
  have hFieldWo : Module.finrank Field Wo =
      Module.finrank IRSProfile.Field Wo := rfl
  have hWoUpper : Module.finrank IRSProfile.Field Wo ≤ 44188803040 := by
    apply right_le_of_codimension_capacity hWoLe hcodim
    rw [hAmbient]
    exact hcapacity
  have hWUpper : Module.finrank Field W ≤ 44188803040 := by
    rw [← hWoFinrank]
    exact hWoUpper
  have hnullity :=
    ContactKernelCommonGCDResearch.Numeric6734.profileA_full_nullity_exact
  omega

theorem derivative_specialization_zero
    (u0 u1 : Index → Field) (S : SelectedInterpolants u0 u1)
    (P : Polynomial Field) (gamma : Field) (support : Finset Index)
    (hcard : support.card = 182032)
    (hPdegree : P.natDegree ≤ 131071)
    (hvalues : ∀ i ∈ support,
      P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
    (hysLower : 54 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualYSWeights S.G)
    (hslopeLower : 12 ≤ wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G)
    (hslopeUpper : wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G ≤ 12) :
    globalSpecialization Field P gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.G) = 0 := by
  classical
  let c := profileAContact S
  let d := profileAComplement S
  have hcUpper : c ≤ 7645343 := by
    have hcaps := (mem_flagGlobalCoefficientBox_iff S.G
      7645344 131071 13754 12 (by norm_num)).mp S.G_flagC
    dsimp only [c]
    exact hcaps.2.2
  have hcLower : 7077822 ≤ c := by
    dsimp only [c]
    exact ContactTwoTailResidualGeneric6734Research.gcd_contact_lower
      S.G 54 12 hysLower hslopeUpper
  have hdPos : 0 < d := by
    change 0 < 7645344 - c
    omega
  have hdUpper : d ≤ 567522 := by
    change 7645344 - c ≤ 567522
    omega
  let W : Submodule Field
      (ContactFlagInterpolation6641Research.globalCoefficientBox
        Field d 131071 84439 0) :=
    ProfileAQuotientRange S hslopeLower
  letI : Module.Free Field W := Module.Free.of_divisionRing Field W
  let u0e : Field → Field := extendIndexFunction u0
  let u1e : Field → Field := extendIndexFunction u1
  let points : Finset Field := support.map IRSProfile.domain
  let h : Field → ℕ := profileALocalOrder S hslopeLower
  have hgap : 50963 ≤ d - ∑ x ∈ points, h x := by
    exact profileA_quotient_gap S support hcard hysLower hslopeLower hslopeUpper
  have htotalUpper : wt
      ContactIdentityResidualGlobalFlagResearch.residualTotalWeights S.G ≤
      1280 := by
    rcases S.G_total_corner with htotal | hys
    · exact htotal
    · omega
  have hysUpper : wt
      ContactIdentityResidualGlobalFlagResearch.residualYSWeights S.G ≤ 55 := by
    rcases S.G_corner with hys | hslope
    · exact hys
    · omega
  have hslopeEq : wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G = 12 := by
    omega
  have hdegreeG2 : S.G.degreeOf 2 = 12 := by
    rw [← originalCumulativeFlag_all]
    exact hslopeEq
  have hderivContact : wt (ContactFactorCaps.contactWeights 131071)
      (MvPolynomial.pderiv (2 : Fin 4) S.G) ≤ c - 131070 := by
    exact pderiv_weight_sub_bound (ContactFactorCaps.contactWeights 131071)
      S.G 2 c le_rfl
  have hderivTotal : wt
      ContactIdentityResidualGlobalFlagResearch.residualTotalWeights
      (MvPolynomial.pderiv (2 : Fin 4) S.G) ≤ 1279 := by
    have hh := pderiv_weight_sub_bound
      ContactIdentityResidualGlobalFlagResearch.residualTotalWeights S.G 2
      (wt ContactIdentityResidualGlobalFlagResearch.residualTotalWeights S.G)
      le_rfl
    change wt ContactIdentityResidualGlobalFlagResearch.residualTotalWeights
      (MvPolynomial.pderiv (2 : Fin 4) S.G) ≤
        wt ContactIdentityResidualGlobalFlagResearch.residualTotalWeights S.G - 1
      at hh
    omega
  have hderivSlope : wt
      ContactIdentityResidualGlobalFlagResearch.residualSWeights
      (MvPolynomial.pderiv (2 : Fin 4) S.G) ≤ 11 := by
    have hh := pderiv_weight_sub_bound
      ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G 2
      (wt ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G) le_rfl
    change wt ContactIdentityResidualGlobalFlagResearch.residualSWeights
      (MvPolynomial.pderiv (2 : Fin 4) S.G) ≤
        wt ContactIdentityResidualGlobalFlagResearch.residualSWeights S.G - 1 at hh
    omega
  have hderivBox : MvPolynomial.pderiv (2 : Fin 4) S.G ∈
      globalCoefficientBox Field (c - 131070 + 1) 131071 1279 11 := by
    have hD : 0 < c - 131070 + 1 := by omega
    apply (mem_flagGlobalCoefficientBox_iff _ _ _ _ _ hD).mpr
    exact ⟨hderivTotal, hderivSlope, by
      simpa only [Nat.add_sub_cancel] using hderivContact⟩
  have hdegree :
      (globalSpecialization Field P gamma
        (MvPolynomial.pderiv (2 : Fin 4) S.G)).natDegree <
          c - 131070 + 1 := by
    exact ContactFlagTranslation6641Research.specialization_natDegree_lt Field
      (c - 131070 + 1) 131071 1279 11
      (MvPolynomial.pderiv (2 : Fin 4) S.G) P gamma
      (by omega) hderivBox hPdegree
  have hlocal : ∀ i ∈ support,
      (Polynomial.X : Polynomial Field) ^ ((42 - h (IRSProfile.domain i)) - 1) ∣
        Polynomial.taylor (IRSProfile.domain i)
          (globalSpecialization Field P gamma
            (MvPolynomial.pderiv (2 : Fin 4) S.G)) := by
    intro i hi
    apply X_pow_dvd_taylor_globalSpecialization_of_scaled
      Field (MvPolynomial.pderiv (2 : Fin 4) S.G) P
      (IRSProfile.domain i) (u0 i) (u1 i) gamma
      ((42 - h (IRSProfile.domain i)) - 1) (hvalues i hi)
    by_cases hhi : h (IRSProfile.domain i) < 42
    · obtain ⟨j, hj⟩ := exists_basis_exact_of_cappedLocalOrder_lt
        d 131071 84439 W (IRSProfile.domain i)
          (u0e (IRSProfile.domain i)) (u1e (IRSProfile.domain i)) hhi
      let Q : W := Module.Free.chooseBasis Field W j
      obtain ⟨v, hv⟩ := Q.property
      have hu0 : u0e (IRSProfile.domain i) = u0 i := by
        change u0 (Function.invFun IRSProfile.domain (IRSProfile.domain i)) = u0 i
        exact congrArg u0
          (Function.leftInverse_invFun IRSProfile.domain.injective i)
      have hu1 : u1e (IRSProfile.domain i) = u1 i := by
        change u1 (Function.invFun IRSProfile.domain (IRSProfile.domain i)) = u1 i
        exact congrArg u1
          (Function.leftInverse_invFun IRSProfile.domain.injective i)
      have hQexact : HasExactScaledOrder Field
          (scaledLocalTranslation Field (IRSProfile.domain i) (u0 i) (u1 i)
            (profileAQuotientPolynomial S v))
          (h (IRSProfile.domain i)) := by
        have hj' : HasExactScaledOrder Field
            (scaledLocalTranslation Field (IRSProfile.domain i)
              (u0e (IRSProfile.domain i)) (u1e (IRSProfile.domain i)) Q.1)
            (h (IRSProfile.domain i)) := by
          simpa [Q, basisScaledPolynomial, scaledTranslationAt,
            h, profileALocalOrder, d, W, u0e, u1e] using hj
        rw [hu0, hu1] at hj'
        have hvval := congrArg Subtype.val hv
        simp only [profileAQuotientMap_apply_val] at hvval
        rwa [hvval]
      apply scaled_pderiv_R_dvd_of_flag_kernel_factor Field
        7645344 131071 84439 12 42 IRSProfile.domain u0 u1
        v.1 v.2 i S.G (profileAQuotientPolynomial S v)
        (h (IRSProfile.domain i))
      · exact profileA_factor S v
      · exact hQexact
    · have heq : h (IRSProfile.domain i) = 42 := by
        have hle := cappedLocalOrder_le d 131071 84439 W
          (IRSProfile.domain i) (u0e (IRSProfile.domain i))
          (u1e (IRSProfile.domain i))
        change h (IRSProfile.domain i) ≤ 42 at hle
        omega
      simp [heq]
  apply globalSpecialization_pderiv_R_eq_zero_of_taylor_divisibility
    Field S.G P gamma IRSProfile.domain support
      (fun i ↦ (42 - h (IRSProfile.domain i)) - 1)
  · exact hlocal
  · let rootSum :=
        ∑ i ∈ support, ((42 - h (IRSProfile.domain i)) - 1)
    change (globalSpecialization Field P gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.G)).natDegree < rootSum
    have hrootLower :
        41 * support.card - ∑ i ∈ support, h (IRSProfile.domain i) ≤
          rootSum := by
      have hpoint : ∀ i ∈ support,
          h (IRSProfile.domain i) ≤ 42 := by
        intro i hi
        dsimp only [h]
        exact cappedLocalOrder_le d 131071 84439 W
          (IRSProfile.domain i) (u0e (IRSProfile.domain i))
          (u1e (IRSProfile.domain i))
      have heach : ∀ i ∈ support,
          41 - h (IRSProfile.domain i) =
            (42 - h (IRSProfile.domain i)) - 1 := by
        intro i hi
        omega
      calc
        41 * support.card - ∑ i ∈ support, h (IRSProfile.domain i) ≤
            ∑ i ∈ support, (41 - h (IRSProfile.domain i)) :=
          forty_one_mul_card_sub_sum_le_sum_sub support
            (fun i ↦ h (IRSProfile.domain i)) hpoint
        _ = rootSum := Finset.sum_congr rfl heach
    have hsumMap : ∑ i ∈ support, h (IRSProfile.domain i) =
        ∑ x ∈ points, h x := by
      dsimp only [points]
      exact (Finset.sum_map support IRSProfile.domain h).symm
    rw [hcard] at hrootLower
    rw [hsumMap] at hrootLower
    have hdEq : d = 7645344 - c := rfl
    have hcd : c + d = 7645344 := by omega
    omega

end
end ProximityPrize.SubmissionLower.RFreeDerivativeCertificate
