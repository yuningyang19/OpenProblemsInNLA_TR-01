import Problem56.PaperV7.GeneralSamplingJoint
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV7
open Problem56.PaperV6

theorem sampling_lower_count_tail_bound_sharp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card ι)
    (hthetaMinus : (1 - ε / 4) * k / Fintype.card ι ≤ 1)
 :
    bernoulliProbability ((1 - ε / 4) * k / Fintype.card ι)
        (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          Real.exp (-(ε ^ 2 * k / 32)) := by
  classical
  let θminus : ℝ := (1 - ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let θplus : ℝ := (1 + ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let a : ℝ := (ε / 4) * (k : ℝ)
  let μminus : ℝ := (Fintype.card ι : ℝ) * θminus
  let μplus : ℝ := (Fintype.card ι : ℝ) * θplus
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk.1
  have hcardNat : 0 < Fintype.card ι := lt_of_lt_of_le hk.1 hk.2
  have hcardReal : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  have hθminus : 0 ≤ θminus ∧ θminus ≤ 1 := by
    constructor
    · dsimp [θminus]
      exact div_nonneg
        (mul_nonneg (by linarith [hε.2]) (Nat.cast_nonneg k))
        hcardReal.le
    · simpa [θminus] using hthetaMinus
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by linarith [hε.1]) (Nat.cast_nonneg k)
  have hμminus : μminus = (1 - ε / 4) * (k : ℝ) := by
    dsimp [μminus, θminus]
    field_simp
  have hμplus : μplus = (1 + ε / 4) * (k : ℝ) := by
    dsimp [μplus, θplus]
    field_simp
  have htailMinus := binomial_tail_bounds_fintype
    (ι := ι) θminus a hθminus ha
  dsimp only at htailMinus
  calc
      bernoulliProbability θminus
          (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          bernoulliProbability θminus (fun b : SignLayer ι ↦
            a ≤ ((transferTrueFinset b).card : ℝ) - μminus) := by
        apply bernoulliProbability_mono θminus hθminus
        intro b hb
        have hbReal : (k : ℝ) < ((transferTrueFinset b).card : ℝ) := by
          exact_mod_cast hb
        dsimp [a]
        rw [hμminus]
        linarith
      _ ≤ Real.exp (-(a ^ 2) /
          (2 * μminus + 2 * a / 3)) := htailMinus.1
      _ ≤ Real.exp (-(ε ^ 2 * k / 32)) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 2 * μminus + 2 * a / 3 := by
          rw [hμminus]
          dsimp [a]
          have hfac : 0 < 1 - ε / 4 := by linarith
          have haPos : 0 < ε / 4 * (k : ℝ) :=
            mul_pos (by linarith) hkReal
          positivity
        have hratio : ε ^ 2 * (k : ℝ) / 32 ≤
            a ^ 2 / (2 * μminus + 2 * a / 3) := by
          rw [le_div_iff₀ hden]
          rw [hμminus]
          dsimp [a]
          field_simp
          nlinarith [sq_pos_of_pos hε.1, sq_pos_of_pos hkReal]
        simpa only [neg_div] using neg_le_neg hratio

theorem sampling_pointwise_saturated_sharp {Ω α : Type*} [Fintype α] [DecidableEq α]
    {r k : ℕ} (X : Ω → Matrix α (Fin r) ℝ)
    (hX : ∀ ω, OrthonormalFrame (X ω))
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hsaturated : 1 ≤ (1 + ε / 4) * k / Fintype.card α) :
    ∀ ω, uniformProbability (fun J : FixedSubset α k ↦
        euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε) ≤
      bernoulliProbability ((1 - ε / 4) * k / Fintype.card α)
        (fun e ↦ euclideanOperatorNorm
          (bernoulliGram ((1 - ε / 4) * k / Fintype.card α) (X ω) e - 1) > ε / 4) +
      Real.exp (-(ε ^ 2 * k / 32)) := by
  classical
  let θminus : ℝ := (1 - ε / 4) * (k : ℝ) /
    (Fintype.card α : ℝ)
  let θplus : ℝ := (1 + ε / 4) * (k : ℝ) /
    (Fintype.card α : ℝ)
  let fixedBad : Ω → FixedSubset α k → Prop := fun ω J ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε
  let minusBad : Ω → SignLayer α → Prop := fun ω b ↦
    euclideanOperatorNorm (bernoulliGram θminus (X ω) b - 1) > ε / 4
  let plusBad : Ω → SignLayer α → Prop := fun ω b ↦
    euclideanOperatorNorm (bernoulliGram θplus (X ω) b - 1) > ε / 4
  let minusCountBad : SignLayer α → Prop := fun b ↦
    k < (transferTrueFinset b).card
  let plusCountBad : SignLayer α → Prop := fun b ↦
    (transferTrueFinset b).card < k
  let fixedIndicator : Ω → FixedSubset α k → ℝ := fun ω J ↦
    if fixedBad ω J then 1 else 0
  let minusIndicator : Ω → SignLayer α → ℝ := fun ω b ↦
    if minusBad ω b then 1 else 0
  let plusIndicator : Ω → SignLayer α → ℝ := fun ω b ↦
    if plusBad ω b then 1 else 0
  let minusCountIndicator : SignLayer α → ℝ := fun b ↦
    if minusCountBad b then 1 else 0
  let plusCountIndicator : SignLayer α → ℝ := fun b ↦
    if plusCountBad b then 1 else 0
  obtain ⟨coupling, hcouplingNonneg, _hcouplingTotal, hcouplingSupport,
      hfixedMarginal, hminusMarginal, hplusMarginal⟩ :=
    uniform_key_nested_coupling_fintype k θminus 1 hk.2
      (sampling_theta_minus ε hε hk).1 (sampling_theta_minus ε hε hk).2 le_rfl
  have hsample (ω : Ω) (J : FixedSubset α k)
      (bminus bplus : SignLayer α) :
      coupling (J, bminus, bplus) * fixedIndicator ω J ≤
        coupling (J, bminus, bplus) *
          (minusIndicator ω bminus + plusIndicator ω bplus +
            minusCountIndicator bminus + plusCountIndicator bplus) := by
    by_cases hc : coupling (J, bminus, bplus) = 0
    · simp [hc]
    have hs := hcouplingSupport (J, bminus, bplus) hc
    have hindicator : fixedIndicator ω J ≤
        minusIndicator ω bminus + plusIndicator ω bplus +
          minusCountIndicator bminus + plusCountIndicator bplus := by
      by_cases hfixedBad : fixedBad ω J
      · by_cases hminusBad : minusBad ω bminus
        · simp [fixedIndicator, minusIndicator, plusIndicator,
            minusCountIndicator, plusCountIndicator, hfixedBad, hminusBad]
          split_ifs <;> norm_num
        · by_cases hplusBad : plusBad ω bplus
          · simp [fixedIndicator, minusIndicator, plusIndicator,
              minusCountIndicator, plusCountIndicator, hfixedBad,
              hminusBad, hplusBad]
            split_ifs <;> norm_num
          · by_cases hminusCount : minusCountBad bminus
            · simp [fixedIndicator, minusIndicator, plusIndicator,
                minusCountIndicator, plusCountIndicator, hfixedBad,
                hminusBad, hplusBad, hminusCount]
              split_ifs <;> norm_num
            · by_cases hplusCount : plusCountBad bplus
              · simp [fixedIndicator, minusIndicator, plusIndicator,
                  minusCountIndicator, plusCountIndicator, hfixedBad,
                  hminusBad, hplusBad, hminusCount, hplusCount]
              · have hbracket :
                    (transferTrueFinset bminus).card ≤ k ∧
                      k ≤ (transferTrueFinset bplus).card :=
                  ⟨Nat.le_of_not_gt hminusCount,
                    Nat.le_of_not_gt hplusCount⟩
                obtain ⟨hminusInclusion, hplusInclusion⟩ := hs.2 hbracket
                have hfixedGood := sampling_sandwich_operatorNorm_conversion
                  (X ω) J bminus bplus ε hε hk
                  hminusInclusion hplusInclusion
                  (le_of_not_gt hminusBad) (le_of_not_gt hplusBad)
                exact False.elim ((not_lt_of_ge hfixedGood) hfixedBad)
      · simp [fixedIndicator, minusIndicator, plusIndicator,
          minusCountIndicator, plusCountIndicator, hfixedBad]
        split_ifs <;> norm_num
    exact mul_le_mul_of_nonneg_left hindicator
      (hcouplingNonneg (J, bminus, bplus))
  have hpoint (ω : Ω) :
      (∑ J, fixedIndicator ω J) /
          Fintype.card (FixedSubset α k) ≤
        bernoulliProbability θminus (minusBad ω) +
          bernoulliProbability 1 (plusBad ω) +
          bernoulliProbability θminus minusCountBad +
          bernoulliProbability 1 plusCountBad := by
    let Wfixed : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * fixedIndicator ω J
    let Wminus : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * minusIndicator ω bminus
    let Wplus : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * plusIndicator ω bplus
    let WminusCount : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * minusCountIndicator bminus
    let WplusCount : ℝ := ∑ J, ∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus) * plusCountIndicator bplus
    have hfixedWeight :
        (∑ J, fixedIndicator ω J) /
            Fintype.card (FixedSubset α k) = Wfixed := by
      calc
        _ = ∑ J, (1 / Fintype.card (FixedSubset α k)) *
            fixedIndicator ω J := by
          simp_rw [div_eq_mul_inv, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro J _
          ring
        _ = Wfixed := by
          exact (weighted_fixed_marginal k coupling hfixedMarginal
            (fixedIndicator ω)).symm
    have hweighted : Wfixed ≤
        Wminus + Wplus + WminusCount + WplusCount := by
      calc
        Wfixed ≤ ∑ J, ∑ bminus, ∑ bplus,
            coupling (J, bminus, bplus) *
              (minusIndicator ω bminus + plusIndicator ω bplus +
                minusCountIndicator bminus +
                plusCountIndicator bplus) := by
          dsimp only [Wfixed]
          apply Finset.sum_le_sum
          intro J _
          apply Finset.sum_le_sum
          intro bminus _
          apply Finset.sum_le_sum
          intro bplus _
          exact hsample ω J bminus bplus
        _ = Wminus + Wplus + WminusCount + WplusCount := by
          dsimp only [Wminus, Wplus, WminusCount, WplusCount]
          simp_rw [mul_add, Finset.sum_add_distrib]
    have hWminus : Wminus =
        bernoulliProbability θminus (minusBad ω) := by
      dsimp only [Wminus]
      simpa [minusIndicator, bernoulliProbability] using
        weighted_minus_marginal k θminus coupling hminusMarginal
          (minusIndicator ω)
    have hWplus : Wplus =
        bernoulliProbability 1 (plusBad ω) := by
      dsimp only [Wplus]
      simpa [plusIndicator, bernoulliProbability] using
        weighted_plus_marginal k 1 coupling hplusMarginal
          (plusIndicator ω)
    have hWminusCount : WminusCount =
        bernoulliProbability θminus minusCountBad := by
      dsimp only [WminusCount]
      calc
        _ = ∑ bminus, bernoulliWeight θminus bminus *
            minusCountIndicator bminus :=
          weighted_minus_marginal k θminus coupling hminusMarginal
            minusCountIndicator
        _ = _ := by
          unfold bernoulliProbability
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : minusCountBad b <;>
            simp [minusCountIndicator, hb]
    have hWplusCount : WplusCount =
        bernoulliProbability 1 plusCountBad := by
      dsimp only [WplusCount]
      calc
        _ = ∑ bplus, bernoulliWeight 1 bplus *
            plusCountIndicator bplus :=
          weighted_plus_marginal k 1 coupling hplusMarginal
            plusCountIndicator
        _ = _ := by
          unfold bernoulliProbability
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : plusCountBad b <;>
            simp [plusCountIndicator, hb]
    calc
      _ = Wfixed := hfixedWeight
      _ ≤ Wminus + Wplus + WminusCount + WplusCount := hweighted
      _ = _ := by rw [hWminus, hWplus, hWminusCount, hWplusCount]
  have htail := sampling_lower_count_tail_bound_sharp k ε hε hk
    (sampling_theta_minus ε hε hk).2
  intro ω
  have hb := hpoint ω
  have hf : uniformProbability (fixedBad ω) =
      (∑ J, fixedIndicator ω J) / Fintype.card (FixedSubset α k) := by
    unfold uniformProbability
    rw [← Finset.sum_boole]
  rw [← hf] at hb
  have hm : bernoulliProbability θminus minusCountBad ≤
      Real.exp (-(ε ^ 2 * k / 32)) := htail
  have hp : bernoulliProbability 1 plusCountBad = 0 := by
    rw [bernoulliProbability_one]
    simp [plusCountBad, transferTrueFinset, not_lt_of_ge hk.2]
  have hpbad : bernoulliProbability 1 (plusBad ω) = 0 := by
    rw [bernoulliProbability_one]
    exact if_neg (not_lt_of_ge (saturated_full_gram (X ω) (hX ω) ε hε hk hsaturated))
  change uniformProbability (fixedBad ω) ≤
    bernoulliProbability θminus (minusBad ω) + Real.exp (-(ε ^ 2 * k / 32))
  rw [hp, hpbad] at hb
  linarith

/-- The exact one-sided saturated probability estimate in the manuscript. -/
theorem general_sampling_saturated_sharp
    {Ω α : Type} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {r k : ℕ}
    (X : Ω → Matrix α (Fin r) ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j))
    (horth : ∀ᵐ ω ∂μ, OrthonormalFrame (X ω))
    (ε γ : ℝ) (he : 0 < ε ∧ ε < 1) (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hs : 1 ≤ (1 + ε / 4) * k / Fintype.card α)
    (hminus : averagedBernoulliFailureProbability μ
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ) :
    averagedFixedFailureProbability (k := k) μ ε X ≤
      γ + Real.exp (-(ε ^ 2 * k / 32)) := by
  let θminus : ℝ := (1 - ε / 4) * k / Fintype.card α
  let F : Ω → ℝ := fun ω ↦ uniformProbability (fun J : FixedSubset α k ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε)
  let B : Ω → ℝ := fun ω ↦ bernoulliProbability θminus (fun e ↦
    euclideanOperatorNorm (bernoulliGram θminus (X ω) e - 1) > ε / 4)
  let c : ℝ := Real.exp (-(ε ^ 2 * k / 32))
  have hF : Integrable F μ := integrable_fixed_failure μ X hX ε
  have hB : Integrable B μ := integrable_bernoulli_failure μ X hX θminus (ε / 4)
  have hb : ∫ ω, F ω ∂μ ≤ ∫ ω, (B ω + c) ∂μ := by
    apply integral_mono_ae hF (hB.add (integrable_const c))
    filter_upwards [horth] with ω hω
    exact sampling_pointwise_saturated_sharp (fun _ : Unit ↦ X ω) (fun _ ↦ hω)
      ε he hk hs ()
  rw [integral_add hB (integrable_const c)] at hb
  simp at hb
  change (∫ ω, B ω ∂μ) ≤ γ at hminus
  change (∫ ω, F ω ∂μ) ≤ γ + c
  linarith

theorem general_sampling_joint_saturated_sharp
    {Ω α : Type} [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {r k : ℕ}
    [MeasurableSpace (FixedSubset α k)] [MeasurableSingletonClass (FixedSubset α k)]
    [MeasurableSpace (SignLayer α)] [MeasurableSingletonClass (SignLayer α)]
    (X : Ω → Matrix α (Fin r) ℝ) (S : Ω → FixedSubset α k)
    (Eminus : Ω → SignLayer α) (ε γ : ℝ)
    (hX : Measurable (fun ω ↦ fun i j ↦ X ω i j))
    (horth : ∀ᵐ ω ∂μ, OrthonormalFrame (X ω))
    (hS : Measurable S) (hEm : Measurable Eminus)
    (hiS : IndepFun (fun ω ↦ fun i j ↦ X ω i j) S μ)
    (hiEm : IndepFun (fun ω ↦ fun i j ↦ X ω i j) Eminus μ)
    (he : 0 < ε ∧ ε < 1) (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hs : 1 ≤ (1 + ε / 4) * k / Fintype.card α)
    (hSMarg : ∀ J, μ.real {ω | S ω = J} = 1 / Fintype.card (FixedSubset α k))
    (hEmMarg : ∀ e, μ.real {ω | Eminus ω = e} =
      bernoulliWeight ((1 - ε / 4) * k / Fintype.card α) e)
    (hminus : μ.real {ω | euclideanOperatorNorm
      (bernoulliGram ((1 - ε / 4) * k / Fintype.card α) (X ω) (Eminus ω) - 1) > ε / 4} ≤ γ) :
    μ.real {ω | euclideanOperatorNorm (fixedSampleGram (X ω) (S ω) - 1) > ε} ≤
      γ + Real.exp (-(ε ^ 2 * k / 32)) := by
  rw [bernoulli_noise_failure_law μ X Eminus hX hEm hiEm _ _
    (sampling_theta_minus ε he hk) hEmMarg] at hminus
  rw [fixed_noise_failure_law μ X S hX hS hiS hk.2 ε hSMarg]
  exact general_sampling_saturated_sharp μ X hX horth ε γ he hk hs hminus

/-- Every quadratic form in the manuscript's deterministic saturated upper chain. -/
theorem saturated_upper_quadraticForm_chain
    {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (J : FixedSubset α k) (ε : ℝ) (he : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hs : 1 ≤ (1 + ε / 4) * k / Fintype.card α) (x : Fin r → ℝ) :
    quadraticForm (fixedSampleGram X J) x ≤
      ((Fintype.card α : ℝ) / k) * (∑ i, (x i)^2) ∧
    ((Fintype.card α : ℝ) / k) * (∑ i, (x i)^2) ≤
      (1 + ε / 4) * (∑ i, (x i)^2) ∧
    (1 + ε / 4) * (∑ i, (x i)^2) ≤
      (1 + ε / 4)^2 * (∑ i, (x i)^2) := by
  classical
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast lt_of_lt_of_le hk.1 hk.2
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hscale : (Fintype.card α : ℝ) / k ≤ 1 + ε / 4 := by
    apply (div_le_iff₀ hkp).mpr
    have h := (le_div_iff₀ hn).mp hs
    nlinarith
  have hnorm : (∑ i : α, ((X.mulVec x) i)^2) = ∑ i, (x i)^2 := by
    have hp : bernoulliProjection (fun _ : α ↦ true) = 1 := by simp [bernoulliProjection]
    have hg : bernoulliGram 1 X (fun _ ↦ true) = 1 := by
      simp [bernoulliGram, hp, OrthonormalFrame] at hX ⊢
      exact hX
    have h := quadraticForm_bernoulliGram_eq (1 : ℝ) X (fun _ ↦ true) x
    rw [hg, quadraticForm_one] at h
    simpa using h.symm
  have hss : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  refine ⟨?_, mul_le_mul_of_nonneg_right hscale hss, ?_⟩
  · rw [quadraticForm_fixedSampleGram_eq]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hn.le hkp.le)
    rw [← hnorm]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> nlinarith [sq_nonneg ((X.mulVec x) i)]
  · apply mul_le_mul_of_nonneg_right _ hss
    nlinarith [sq_nonneg (ε / 4)]

end Problem56.PaperV7
