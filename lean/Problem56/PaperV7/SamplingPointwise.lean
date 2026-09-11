import Problem56.PaperV7.SamplingSaturated

open scoped BigOperators Matrix
namespace Problem56.PaperV7

theorem sampling_pointwise_saturated {Ω α : Type*} [Fintype α] [DecidableEq α]
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
      Real.exp (-(ε ^ 2 * k / 48)) := by
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
  have htail := sampling_lower_count_tail_bound k ε hε hk
    (sampling_theta_minus ε hε hk).2
  intro ω
  have hb := hpoint ω
  have hf : uniformProbability (fixedBad ω) =
      (∑ J, fixedIndicator ω J) / Fintype.card (FixedSubset α k) := by
    unfold uniformProbability
    rw [← Finset.sum_boole]
  rw [← hf] at hb
  have hm : bernoulliProbability θminus minusCountBad ≤
      Real.exp (-(ε ^ 2 * k / 48)) := htail
  have hp : bernoulliProbability 1 plusCountBad = 0 := by
    rw [bernoulliProbability_one]
    simp [plusCountBad, transferTrueFinset, not_lt_of_ge hk.2]
  have hpbad : bernoulliProbability 1 (plusBad ω) = 0 := by
    rw [bernoulliProbability_one]
    exact if_neg (not_lt_of_ge (saturated_full_gram (X ω) (hX ω) ε hε hk hsaturated))
  change uniformProbability (fixedBad ω) ≤
    bernoulliProbability θminus (minusBad ω) + Real.exp (-(ε ^ 2 * k / 48))
  rw [hp, hpbad] at hb
  linarith

end Problem56.PaperV7
