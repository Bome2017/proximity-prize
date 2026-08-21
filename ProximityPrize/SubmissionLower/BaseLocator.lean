import ProximityPrize.SubmissionLower.Puncture

/-!
# Base-field locator constraint at the first post-UDR cell

The Berlekamp--Welch kernel is normally formed over the sextic challenge
field.  For this concrete profile that loses essential information: every
evaluation point is the image of a KoalaBear base-field point.  Consequently
the monic locator of any actual Hamming error set is obtained by coefficient-
wise base extension from `KoalaBear.Field[X]`.

This is the restriction that distinguishes a genuine decoding kernel vector
from the automatic 33-dimensional kernel of the relaxed sextic-field BW
matrix at error cell 65552.
-/

namespace ProximityPrize.SubmissionLower.BaseLocator

open Polynomial
open ProximityPrize.Benchmark
open Code CoreDefinitions ProximityGap

/-- The error locator before extending scalars to the sextic challenge field. -/
noncomputable def baseLocator (D : Finset IRSProfile.Index) :
    Polynomial _root_.KoalaBear.Field :=
  ∏ i ∈ D,
    ((Polynomial.X : Polynomial _root_.KoalaBear.Field) -
      Polynomial.C (IRSProfile.baseNttDomain.node i))

/-- The same locator written directly over the sextic challenge field. -/
noncomputable def extensionLocator (D : Finset IRSProfile.Index) :
    Polynomial IRSProfile.Field :=
  ∏ i ∈ D,
    ((Polynomial.X : Polynomial IRSProfile.Field) -
      Polynomial.C (IRSProfile.domain i))

/-- Actual support locators are coefficient-wise extensions of base-field
locators; they do not range over arbitrary sextic-field coefficient vectors. -/
theorem extensionLocator_eq_map (D : Finset IRSProfile.Index) :
    extensionLocator D =
      (baseLocator D).map
        (algebraMap _root_.KoalaBear.Field IRSProfile.Field) := by
  classical
  rw [extensionLocator, baseLocator, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [IRSProfile.domain, CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- The base-field error locator is monic. -/
theorem baseLocator_monic (D : Finset IRSProfile.Index) :
    (baseLocator D).Monic := by
  classical
  simpa [baseLocator] using
    (Polynomial.monic_prod_X_sub_C
      (b := fun i : IRSProfile.Index => IRSProfile.baseNttDomain.node i)
      (s := D))

/-- Its degree is exactly the number of error positions. -/
theorem baseLocator_natDegree (D : Finset IRSProfile.Index) :
    (baseLocator D).natDegree = D.card := by
  classical
  unfold baseLocator
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i hi
    exact Polynomial.monic_X_sub_C _

/-- Scalar extension preserves the exact locator degree. -/
theorem extensionLocator_natDegree (D : Finset IRSProfile.Index) :
    (extensionLocator D).natDegree = D.card := by
  rw [extensionLocator_eq_map,
    (baseLocator_monic D).natDegree_map, baseLocator_natDegree]

/-- The extended locator remains monic, hence nonzero. -/
theorem extensionLocator_monic (D : Finset IRSProfile.Index) :
    (extensionLocator D).Monic := by
  rw [extensionLocator_eq_map]
  exact Polynomial.Monic.map
    (algebraMap _root_.KoalaBear.Field IRSProfile.Field) (baseLocator_monic D)

/-- Error and agreement locators partition the full nodal polynomial over
the challenge field as well as over the base field. -/
theorem extensionLocator_mul_compl (D : Finset IRSProfile.Index) :
    extensionLocator D * extensionLocator Dᶜ =
      extensionLocator (Finset.univ : Finset IRSProfile.Index) := by
  simpa only [extensionLocator] using
    (Finset.prod_mul_prod_compl D
      (fun i : IRSProfile.Index =>
        ((Polynomial.X : Polynomial IRSProfile.Field) -
          Polynomial.C (IRSProfile.domain i))))

/-- The unique degree-below-`n` polynomial representing a received word on
the full IRS evaluation domain. -/
noncomputable def receivedPolynomial
    (u : IRSProfile.Index → IRSProfile.Field) : Polynomial IRSProfile.Field :=
  Lagrange.interpolate Finset.univ IRSProfile.domain u

/-- The received polynomial recovers the word at every NTT node. -/
theorem receivedPolynomial_eval
    (u : IRSProfile.Index → IRSProfile.Field) (i : IRSProfile.Index) :
    (receivedPolynomial u).eval (IRSProfile.domain i) = u i := by
  exact Lagrange.eval_interpolate_at_node u IRSProfile.domain.injective.injOn
    (Finset.mem_univ i)

/-- The received representative has degree strictly below the domain size. -/
theorem receivedPolynomial_natDegree_lt
    (u : IRSProfile.Index → IRSProfile.Field) :
    (receivedPolynomial u).natDegree < Fintype.card IRSProfile.Index := by
  by_cases hzero : receivedPolynomial u = 0
  · simp [hzero, IRSProfile.Index]
  · rw [Polynomial.natDegree_lt_iff_degree_lt hzero]
    exact Lagrange.degree_interpolate_lt u IRSProfile.domain.injective.injOn

/-- Interpolation preserves the affine dependence on the slope. -/
theorem receivedPolynomial_affine_line
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field) :
    receivedPolynomial (fun i => U 0 i + gamma * U 1 i) =
      receivedPolynomial (U 0) +
        Polynomial.C gamma * receivedPolynomial (U 1) := by
  classical
  symm
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (receivedPolynomial (U 0) +
      Polynomial.C gamma * receivedPolynomial (U 1))
    (receivedPolynomial (fun i => U 0 i + gamma * U 1 i))
    IRSProfile.domain.injective ?_ ?_
  · intro i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      receivedPolynomial_eval]
  · apply max_lt
    · exact (Polynomial.natDegree_add_le _ _).trans_lt
        (max_lt (receivedPolynomial_natDegree_lt _)
          ((Polynomial.natDegree_C_mul_le gamma _).trans_lt
            (receivedPolynomial_natDegree_lt _)))
    · exact receivedPolynomial_natDegree_lt _

/-- A local root-product divisibility lemma.  `TargetLower` exposes the
polynomial root API but not CompPoly's later convenience wrapper. -/
lemma prod_X_sub_C_dvd_of_eval_zero {F ι : Type*} [Field F]
    (s : Finset ι) (a : ι → F) (hinj : Set.InjOn a s)
    (p : Polynomial F) (hroot : ∀ i ∈ s, p.eval (a i) = 0) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) ∣ p := by
  classical
  exact Finset.prod_dvd_of_coprime
    (fun _ hi _ hj hij =>
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr (hij <| hinj hi hj ·)).isUnit)
    (fun i hi => Polynomial.dvd_iff_isRoot.mpr (hroot i hi))

/-- A genuine error locator and its complementary agreement locator multiply
to the fixed full NTT nodal polynomial.  Thus actual locators occupy its
monic divisors, a far smaller set than arbitrary base-coefficient vectors. -/
theorem baseLocator_mul_compl (D : Finset IRSProfile.Index) :
    baseLocator D * baseLocator Dᶜ =
      baseLocator (Finset.univ : Finset IRSProfile.Index) := by
  simpa only [baseLocator] using
    (Finset.prod_mul_prod_compl D
      (fun i : IRSProfile.Index =>
        ((Polynomial.X : Polynomial _root_.KoalaBear.Field) -
          Polynomial.C (IRSProfile.baseNttDomain.node i))))

/-- In particular, every genuine error locator divides the full NTT nodal
polynomial. -/
theorem baseLocator_dvd_full (D : Finset IRSProfile.Index) :
    baseLocator D ∣
      baseLocator (Finset.univ : Finset IRSProfile.Index) := by
  refine ⟨baseLocator Dᶜ, ?_⟩
  exact (baseLocator_mul_compl D).symm

/-- Every coefficient of a genuine locator is in the embedded base field. -/
theorem coeff_extensionLocator_is_base
    (D : Finset IRSProfile.Index) (n : ℕ) :
    ∃ a : _root_.KoalaBear.Field,
      (extensionLocator D).coeff n =
        algebraMap _root_.KoalaBear.Field IRSProfile.Field a := by
  refine ⟨(baseLocator D).coeff n, ?_⟩
  rw [extensionLocator_eq_map, Polynomial.coeff_map]

/-- The exact BW excess at the score-53.14 cell. -/
theorem post_udr_kernel_excess :
    ((65552 + 1) + (65552 + IRSProfile.baseDimension)) -
        Fintype.card IRSProfile.Index = 33 := by
  norm_num [IRSProfile.baseDimension, IRSProfile.Index]

/-- After imposing a close polynomial of degree `< 2^17`, the residual
quotient has degree at most 31: the 32-dimensional defect that must be
controlled, rather than charged as 32 independent entropy losses. -/
theorem residual_quotient_degree_budget :
    (65552 + IRSProfile.baseDimension - 1) - (262144 - 65552) = 31 := by
  norm_num [IRSProfile.baseDimension]

/-- After eliminating the `Q = E * P` block, 65520 sextic syndrome
equations remain. -/
theorem residual_syndrome_rows :
    Fintype.card IRSProfile.Index -
        (65552 + IRSProfile.baseDimension) = 65520 := by
  norm_num [IRSProfile.Index, IRSProfile.baseDimension]

/-- Splitting those rows into the six explicit KoalaBear coordinates gives
393120 base-field scalar equations. -/
theorem residual_base_scalar_equations : 6 * 65520 = 393120 := by
  norm_num

/-- A degree-at-most-65552 base locator has 65553 scalar coefficients. -/
theorem base_locator_scalar_unknowns : 65552 + 1 = 65553 := by
  norm_num

/-- The resulting base-locator system is overdetermined by 327567 scalar
equations.  This is a dimension ledger, not an assertion that every such
system has full rank. -/
theorem base_locator_overdetermination : 393120 - 65553 = 327567 := by
  norm_num

/-- The full mixed BW system has 65553 base-field locator coefficients and
196624 sextic `Q` coefficients.  The latter count is `e + k`, not
`e + k + 1`, because `natDegree (E * P) < e + k`. -/
theorem mixed_bw_scalar_unknowns :
    (65552 + 1) + 6 * (65552 + IRSProfile.baseDimension) = 1245297 := by
  norm_num [IRSProfile.baseDimension]

/-- Six scalar equations at each of the 262144 evaluation points leave the
same 327567-equation excess in the full mixed system. -/
theorem mixed_bw_overdetermination :
    6 * Fintype.card IRSProfile.Index - 1245297 = 327567 := by
  norm_num [IRSProfile.Index]

/-- The first radius whose score can round up to 53.14 bits. -/
noncomputable def cellRadius : NNReal := (262209 : NNReal) / 1048576

theorem cellRadius_floor :
    ⌊(cellRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 65552 := by
  norm_num [cellRadius, IRSProfile.Index]

/-- A bad slope at the 53.14 cell admits an exact 65552-point error
locator, and that locator is the base-field locator defined above.  The
identity is the support-aware BW equation before the usual relaxation to an
arbitrary sextic-coefficient locator. -/
theorem bad_slope_has_base_locator_relation
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (cellRadius : ℝ)) :
    ∃ (S D : Finset IRSProfile.Index) (P : Polynomial IRSProfile.Field),
      S.card = 196592 ∧
      D = Sᶜ ∧
      D.card = 65552 ∧
      P.natDegree < IRSProfile.baseDimension ∧
      ∀ i : IRSProfile.Index,
        (extensionLocator D).eval (IRSProfile.domain i) *
            (U 0 i + gamma * U 1 i) =
          (extensionLocator D * P).eval (IRSProfile.domain i) := by
  classical
  obtain ⟨S, hScard, hcomb, _hbad⟩ :=
    ProximityPrize.SubmissionLower.exists_exact_mca_support_rs
      (domain := IRSProfile.domain) (k := IRSProfile.baseDimension)
      (a := 196592) (by norm_num [IRSProfile.baseDimension])
      (by norm_num [IRSProfile.baseDimension])
      (U := U) (γ := gamma) (δ := (cellRadius : ℝ)) (by
        intro T hT
        have hcomp :=
          (mul_one_sub_le_card_iff_sub_card_le_floor T
            (show (0 : ℝ) ≤ (cellRadius : ℝ) by
              norm_num [cellRadius])).mp hT
        rw [cellRadius_floor] at hcomp
        have hn : Fintype.card IRSProfile.Index = 262144 := by
          norm_num [IRSProfile.Index]
        rw [hn] at hcomp
        omega)
      (by simpa [IRSProfile.baseCode] using hgamma)
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨c, hc, hproj⟩ := hcomb
  change c ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨P, hPdeg, rfl⟩ := hc
  let D : Finset IRSProfile.Index := Sᶜ
  have hDcard : D.card = 65552 := by
    dsimp [D]
    rw [Finset.card_compl, hScard]
    norm_num [IRSProfile.Index]
  refine ⟨S, D, P, hScard, rfl, hDcard, ?_, ?_⟩
  · by_cases hP : P = 0
    · simp [hP, IRSProfile.baseDimension]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hPdeg
  · intro i
    rw [Polynomial.eval_mul]
    by_cases hiS : i ∈ S
    · have heq := congrFun hproj ⟨i, hiS⟩
      have hfold : U 0 i + gamma * U 1 i = P.eval (IRSProfile.domain i) := by
        simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints,
          AffineLineGenerator, Fin.sum_univ_two] using heq
      rw [hfold]
    · have hiD : i ∈ D := by simp [D, hiS]
      have hEzero : (extensionLocator D).eval (IRSProfile.domain i) = 0 := by
        rw [extensionLocator, Polynomial.eval_prod]
        apply Finset.prod_eq_zero hiD
        simp
      simp [hEzero]

/-- A full-domain locator relation forces the complementary Gao factor. -/
theorem locator_relation_has_gao_factorization
    (S D : Finset IRSProfile.Index) (P R : Polynomial IRSProfile.Field)
    (hScard : S.card = 196592) (hD : D = Sᶜ)
    (hPdeg : P.natDegree < IRSProfile.baseDimension)
    (hRdeg : R.natDegree < Fintype.card IRSProfile.Index)
    (hrel : ∀ i : IRSProfile.Index,
      (extensionLocator D).eval (IRSProfile.domain i) *
          R.eval (IRSProfile.domain i) =
        (extensionLocator D * P).eval (IRSProfile.domain i)) :
    ∃ H : Polynomial IRSProfile.Field,
      R = P + extensionLocator S * H ∧ H.natDegree < 65552 := by
  classical
  have hroot : ∀ i ∈ (Finset.univ : Finset IRSProfile.Index),
      (extensionLocator D * (R - P)).eval (IRSProfile.domain i) = 0 := by
    intro i hi
    have h := hrel i
    rw [Polynomial.eval_mul] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_sub]
    rw [mul_sub, h, sub_self]
  have hdvd : extensionLocator (Finset.univ : Finset IRSProfile.Index) ∣
      extensionLocator D * (R - P) := by
    simpa only [extensionLocator] using
      (prod_X_sub_C_dvd_of_eval_zero Finset.univ IRSProfile.domain
        IRSProfile.domain.injective.injOn
        (extensionLocator D * (R - P)) hroot)
  obtain ⟨H, hH⟩ := hdvd
  have hcancel :
      extensionLocator D * (extensionLocator Dᶜ * H) =
        extensionLocator D * (R - P) := by
    calc
      extensionLocator D * (extensionLocator Dᶜ * H) =
          (extensionLocator D * extensionLocator Dᶜ) * H := by
            rw [mul_assoc]
      _ = extensionLocator (Finset.univ : Finset IRSProfile.Index) * H := by
            rw [extensionLocator_mul_compl]
      _ = extensionLocator D * (R - P) := hH.symm
  have hfactor : extensionLocator Dᶜ * H = R - P :=
    mul_left_cancel₀ (extensionLocator_monic D).ne_zero hcancel
  have hDcomp : Dᶜ = S := by
    simpa [hD]
  have hPdegFull : P.natDegree < Fintype.card IRSProfile.Index := by
    exact lt_trans hPdeg (by norm_num [IRSProfile.baseDimension, IRSProfile.Index])
  have hdiffdeg : (R - P).natDegree < Fintype.card IRSProfile.Index :=
    (Polynomial.natDegree_sub_le R P).trans_lt (max_lt hRdeg hPdegFull)
  have hHdeg : H.natDegree < 65552 := by
    by_cases hHzero : H = 0
    · simp [hHzero]
    · have hproddeg : (extensionLocator Dᶜ * H).natDegree <
          Fintype.card IRSProfile.Index := by
        rw [hfactor]
        exact hdiffdeg
      rw [Polynomial.natDegree_mul (extensionLocator_monic Dᶜ).ne_zero hHzero,
        extensionLocator_natDegree, hDcomp, hScard] at hproddeg
      norm_num [IRSProfile.Index] at hproddeg
      omega
  have hnormal : R = P + extensionLocator S * H := by
    calc
      R = P + (R - P) := by ring
      _ = P + extensionLocator Dᶜ * H := by rw [← hfactor]
      _ = P + extensionLocator S * H := by rw [hDcomp]
  exact ⟨H, hnormal, hHdeg⟩

/-- Exact Gao normal form for an MCA-bad slope.  The full received
interpolant differs from the close codeword by the agreement locator times a
polynomial of degree below the error budget.  In particular the large factor
is not arbitrary: it is the scalar extension of a monic base-field divisor of
the fixed full NTT nodal polynomial. -/
theorem bad_slope_has_gao_factorization
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (cellRadius : ℝ)) :
    ∃ (S D : Finset IRSProfile.Index) (P H : Polynomial IRSProfile.Field),
      S.card = 196592 ∧
      D = Sᶜ ∧
      D.card = 65552 ∧
      P.natDegree < IRSProfile.baseDimension ∧
      (extensionLocator S).natDegree = 196592 ∧
      baseLocator S ∣
        baseLocator (Finset.univ : Finset IRSProfile.Index) ∧
      receivedPolynomial (fun i => U 0 i + gamma * U 1 i) =
        P + extensionLocator S * H ∧
      H.natDegree < 65552 := by
  classical
  obtain ⟨S, D, P, hScard, hD, hDcard, hPdeg, hrel⟩ :=
    bad_slope_has_base_locator_relation U gamma hgamma
  let R : Polynomial IRSProfile.Field :=
    receivedPolynomial (fun i => U 0 i + gamma * U 1 i)
  have hRdeg : R.natDegree < Fintype.card IRSProfile.Index := by
    exact receivedPolynomial_natDegree_lt _
  have hrelR : ∀ i : IRSProfile.Index,
      (extensionLocator D).eval (IRSProfile.domain i) *
          R.eval (IRSProfile.domain i) =
        (extensionLocator D * P).eval (IRSProfile.domain i) := by
    intro i
    simpa only [R, receivedPolynomial_eval] using hrel i
  obtain ⟨H, hnormal, hHdeg⟩ := locator_relation_has_gao_factorization
    S D P R hScard hD hPdeg hRdeg hrelR
  refine ⟨S, D, P, H, hScard, hD, hDcard, hPdeg, ?_,
    baseLocator_dvd_full S, ?_, hHdeg⟩
  · rw [extensionLocator_natDegree, hScard]
  · exact hnormal

/-- Incidence form of the Gao cut: the slope appears only as the scalar
coefficient of the fixed polynomial `receivedPolynomial (U 1)`. -/
theorem bad_slope_has_affine_gao_incidence
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (cellRadius : ℝ)) :
    ∃ (S : Finset IRSProfile.Index) (P H : Polynomial IRSProfile.Field),
      S.card = 196592 ∧
      P.natDegree < IRSProfile.baseDimension ∧
      H.natDegree < 65552 ∧
      baseLocator S ∣
        baseLocator (Finset.univ : Finset IRSProfile.Index) ∧
      receivedPolynomial (U 0) +
          Polynomial.C gamma * receivedPolynomial (U 1) =
        P + extensionLocator S * H := by
  obtain ⟨S, D, P, H, hScard, hD, hDcard, hPdeg, hAdeg,
    hdiv, hnormal, hHdeg⟩ := bad_slope_has_gao_factorization U gamma hgamma
  refine ⟨S, P, H, hScard, hPdeg, hHdeg, hdiv, ?_⟩
  exact (receivedPolynomial_affine_line U gamma).symm.trans hnormal

/-- Coefficient form of the base-restricted BW system.  A bad slope supplies
a nonzero vector `a` over the KoalaBear base field and a vector `b` over the
sextic field.  The equation is then split into all six base coordinates.

This is the exact rank problem hidden by the automatic 33-dimensional
kernel of the unrestricted sextic BW matrix. -/
theorem bad_slope_has_base_coefficient_system
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (cellRadius : ℝ)) :
    ∃ (a : Fin 65553 → _root_.KoalaBear.Field)
        (b : Fin (65552 + IRSProfile.baseDimension) → IRSProfile.Field),
      a ≠ 0 ∧
      a ⟨65552, by norm_num⟩ = 1 ∧
      ∀ (i : IRSProfile.Index) (c : Fin 6),
        CompPoly.Extension.Ext.coeff
            ((∑ t, algebraMap _root_.KoalaBear.Field IRSProfile.Field (a t) *
                IRSProfile.domain i ^ (t : ℕ)) *
              (U 0 i + gamma * U 1 i)) c =
          CompPoly.Extension.Ext.coeff
            (∑ s, b s * IRSProfile.domain i ^ (s : ℕ)) c := by
  classical
  obtain ⟨S, D, P, hScard, hD, hDcard, hPdeg, hrel⟩ :=
    bad_slope_has_base_locator_relation U gamma hgamma
  let a : Fin 65553 → _root_.KoalaBear.Field :=
    fun t => (baseLocator D).coeff (t : ℕ)
  let Q : Polynomial IRSProfile.Field := extensionLocator D * P
  let b : Fin (65552 + IRSProfile.baseDimension) → IRSProfile.Field :=
    fun s => Q.coeff (s : ℕ)
  have hEdeg : (extensionLocator D).natDegree < 65553 := by
    rw [extensionLocator_natDegree, hDcard]
    norm_num
  have hQdeg : Q.natDegree < 65552 + IRSProfile.baseDimension := by
    have hmul : Q.natDegree ≤
        (extensionLocator D).natDegree + P.natDegree := by
      simpa [Q] using
        (Polynomial.natDegree_mul_le
          (p := extensionLocator D) (q := P))
    rw [extensionLocator_natDegree, hDcard] at hmul
    omega
  let top : Fin 65553 := ⟨65552, by norm_num⟩
  have htop : a top = 1 := by
    have hlc : (baseLocator D).leadingCoeff = 1 :=
      (baseLocator_monic D).leadingCoeff
    simpa [a, top, Polynomial.leadingCoeff, baseLocator_natDegree,
      hDcard] using hlc
  have ha_ne : a ≠ 0 := by
    intro ha
    have hz := congrFun ha top
    simp [htop] at hz
  refine ⟨a, b, ha_ne, by simpa [top] using htop, ?_⟩
  intro i c
  have hsumE :
      (∑ t : Fin 65553,
          algebraMap _root_.KoalaBear.Field IRSProfile.Field (a t) *
            IRSProfile.domain i ^ (t : ℕ)) =
        (extensionLocator D).eval (IRSProfile.domain i) := by
    have hfin :
        (∑ t : Fin 65553,
            algebraMap _root_.KoalaBear.Field IRSProfile.Field (a t) *
              IRSProfile.domain i ^ (t : ℕ)) =
          ∑ n ∈ Finset.range 65553,
            (extensionLocator D).coeff n * IRSProfile.domain i ^ n := by
      simpa [a, extensionLocator_eq_map] using
        (Fin.sum_univ_eq_sum_range
          (f := fun n : ℕ =>
            (extensionLocator D).coeff n * IRSProfile.domain i ^ n)
          (n := 65553))
    exact hfin.trans
      (Polynomial.eval_eq_sum_range' (p := extensionLocator D)
        (n := 65553) hEdeg (IRSProfile.domain i)).symm
  have hsumQ :
      (∑ s : Fin (65552 + IRSProfile.baseDimension),
          b s * IRSProfile.domain i ^ (s : ℕ)) =
        Q.eval (IRSProfile.domain i) := by
    have hfin :
        (∑ s : Fin (65552 + IRSProfile.baseDimension),
            b s * IRSProfile.domain i ^ (s : ℕ)) =
          ∑ n ∈ Finset.range (65552 + IRSProfile.baseDimension),
            Q.coeff n * IRSProfile.domain i ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range
          (f := fun n : ℕ => Q.coeff n * IRSProfile.domain i ^ n)
          (n := 65552 + IRSProfile.baseDimension))
    exact hfin.trans
      (Polynomial.eval_eq_sum_range' (p := Q)
        (n := 65552 + IRSProfile.baseDimension) hQdeg
          (IRSProfile.domain i)).symm
  rw [hsumE, hsumQ]
  exact congrArg (fun x : IRSProfile.Field =>
    CompPoly.Extension.Ext.coeff x c) (by simpa [Q] using hrel i)

/-- Evaluation of a base-field locator coefficient vector at one domain
point, after extending its coefficients to the sextic field. -/
def evalBaseLocatorVector
    (a : Fin 65553 → _root_.KoalaBear.Field) (i : IRSProfile.Index) :
    IRSProfile.Field :=
  ∑ t, algebraMap _root_.KoalaBear.Field IRSProfile.Field (a t) *
    IRSProfile.domain i ^ (t : ℕ)

/-- Evaluation of the sextic `Q` coefficient vector at one domain point. -/
def evalQuotientVector
    (b : Fin (65552 + IRSProfile.baseDimension) → IRSProfile.Field)
    (i : IRSProfile.Index) : IRSProfile.Field :=
  ∑ s, b s * IRSProfile.domain i ^ (s : ℕ)

/-- A nonzero base-locator vector in the mixed BW kernel. -/
structure BaseBWWitness
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field) where
  locator : Fin 65553 → _root_.KoalaBear.Field
  quotient : Fin (65552 + IRSProfile.baseDimension) → IRSProfile.Field
  locator_ne : locator ≠ 0
  locator_top : locator ⟨65552, by norm_num⟩ = 1
  equations : ∀ i : IRSProfile.Index,
    evalBaseLocatorVector locator i * (U 0 i + gamma * U 1 i) =
      evalQuotientVector quotient i

/-- Rank-defect locus of the mixed base/sextic BW system.  Unlike the
unrestricted sextic matrix, this predicate does not hold merely because the
raw column count exceeds the evaluation-domain size. -/
def BaseBWSingular
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field) : Prop :=
  Nonempty (BaseBWWitness U gamma)

/-- Every MCA-bad slope at the 53.14 cell lies in the base-restricted rank
defect locus. -/
theorem bad_slope_mem_baseBWSingular
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (cellRadius : ℝ)) :
    BaseBWSingular U gamma := by
  obtain ⟨a, b, ha, htop, hcoeff⟩ :=
    bad_slope_has_base_coefficient_system U gamma hgamma
  refine ⟨{
    locator := a
    quotient := b
    locator_ne := ha
    locator_top := htop
    equations := ?_ }⟩
  intro i
  apply CompPoly.Extension.Ext.ext
  intro c
  simpa only [evalBaseLocatorVector, evalQuotientVector] using hcoeff i c

/-- Exact MCA numerator available after reserving four field elements for
the squared-code list term in the 53.14 reduction. -/
def rankDefectBudget : ℕ := 274980728111395083

set_option maxRecDepth 100000 in
/-- The rank-defect budget plus the four-element list term fits exactly
under the `2^-128` field-cardinality target. -/
theorem rankDefectBudget_with_list_fits :
    (rankDefectBudget + 4) * 2 ^ 128 ≤
      Fintype.card IRSProfile.Field := by
  norm_num [rankDefectBudget, IRSProfile.Field, KoalaBear.Ext6]

end ProximityPrize.SubmissionLower.BaseLocator
