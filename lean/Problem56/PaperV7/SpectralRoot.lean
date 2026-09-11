import Problem56.SpectralRoot

/-! Full-density spectral-root estimate for manuscript v7, Lemma 2. -/

namespace Problem56.PaperV7

theorem bad_spectral_edge_large_root
    (lam δ θ η : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hδ : 0 < δ)
    (hθ : 0 < θ ∧ θ < 1) (hη : 0 < η ∧ η < 1)
    (hsmall : δ ≤ θ * η ^ 2 / 64)
    (hbad : |lam - θ| > θ * η) :
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    let t := lam - δ - θ + 2 * δ * θ
    |t| > 63 * (θ * η) / 64 ∧
    (lam = 0 → (1 - δ) * θ > θ * η / 2) ∧
    (lam = 1 → (1 - δ) * (1 - θ) > θ * η / 2) ∧
    (0 < lam → lam < 1 →
      ∃ z₁ z₂ : ℝ, z₁ + z₂ = t ∧ z₁ * z₂ = a2 ∧
        max |z₁| |z₂| > θ * η / 2) := by
  dsimp only
  let q : ℝ := θ * η
  let A : ℝ := δ * (1 - δ) * θ * (1 - θ)
  let T : ℝ := lam - δ - θ + 2 * δ * θ
  change |T| > 63 * q / 64 ∧
    (lam = 0 → (1 - δ) * θ > q / 2) ∧
    (lam = 1 → (1 - δ) * (1 - θ) > q / 2) ∧
    (0 < lam → lam < 1 →
      ∃ z₁ z₂ : ℝ, z₁ + z₂ = T ∧ z₁ * z₂ = A ∧
        max |z₁| |z₂| > q / 2)
  have hq : q = θ * η := rfl
  have hqpos : 0 < q := by
    rw [hq]
    exact mul_pos hθ.1 hη.1
  have hηsq_lt : η ^ 2 < η := by
    nlinarith [mul_pos hη.1 (sub_pos.mpr hη.2)]
  have hδq : δ < q / 64 := by
    have hmul : θ * η ^ 2 < θ * η :=
      mul_lt_mul_of_pos_left hηsq_lt hθ.1
    rw [hq]
    nlinarith
  have hqone : q < 1 := by
    rw [hq]
    calc
      θ * η < θ * 1 := mul_lt_mul_of_pos_left hη.2 hθ.1
      _ < 1 := by simpa using hθ.2
  have hδhalf : δ < 1 / 2 := by nlinarith
  have hδone : δ < 1 := hδhalf.trans (by norm_num)
  have hTdecomp : lam - θ = T + δ * (1 - 2 * θ) := by
    simp only [T]
    ring
  have hy_le : |δ * (1 - 2 * θ)| ≤ δ := by
    rw [abs_mul, abs_of_pos hδ]
    have habs : |1 - 2 * θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    simpa using mul_le_mul_of_nonneg_left habs hδ.le
  have hTtri : |lam - θ| ≤ |T| + |δ * (1 - 2 * θ)| := by
    rw [hTdecomp]
    exact abs_add_le _ _
  have hTlarge : |T| > 63 * q / 64 := by nlinarith
  have hleftBase : η / 2 < 1 - δ := by nlinarith
  have hendpointZero : (1 - δ) * θ > q / 2 := by
    have h := mul_lt_mul_of_pos_right hleftBase hθ.1
    rw [hq]
    nlinarith
  refine ⟨hTlarge, ?_, ?_, ?_⟩
  · intro _
    exact hendpointZero
  · intro hone
    have hbadOne : q < 1 - θ := by
      have hh : |1 - θ| > θ * η := by simpa [hone] using hbad
      rw [abs_of_pos (sub_pos.mpr hθ.2)] at hh
      exact hh
    have hfirst : q / 2 < (1 - θ) / 2 := by linarith
    have hsecond : (1 - θ) / 2 ≤ (1 - δ) * (1 - θ) := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - δ by linarith) (sub_nonneg.mpr hθ.2.le)]
    exact hfirst.trans_le hsecond
  · intro hlam0 hlam1
    have hA0 : 0 ≤ A := by
      simp only [A]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hδ.le (by linarith)) hθ.1.le) (by linarith)
    have hA_le_delta_theta : A ≤ δ * θ := by
      simp only [A]
      have hδfactor : δ * (1 - δ) ≤ δ := by
        nlinarith [mul_pos hδ (sub_pos.mpr hδone)]
      have hθfactor : θ * (1 - θ) ≤ θ := by
        nlinarith [mul_pos hθ.1 (by linarith : 0 < 1 - θ)]
      calc
        δ * (1 - δ) * θ * (1 - θ) =
            (δ * (1 - δ)) * (θ * (1 - θ)) := by ring
        _ ≤ δ * θ :=
          mul_le_mul hδfactor hθfactor (mul_nonneg hθ.1.le (by linarith)) hδ.le
    have hdeltaTheta : δ * θ ≤ q ^ 2 / 64 := by
      calc
        δ * θ ≤ (θ * η ^ 2 / 64) * θ :=
          mul_le_mul_of_nonneg_right hsmall hθ.1.le
        _ = q ^ 2 / 64 := by simp only [q]; ring
    have hAq : A ≤ q ^ 2 / 64 := hA_le_delta_theta.trans hdeltaTheta
    let D : ℝ := T ^ 2 - 4 * A
    have hc0 : 0 ≤ 63 * q / 64 := by positivity
    have hTsq : (63 * q / 64) ^ 2 < T ^ 2 := by
      have hs := (sq_lt_sq₀ hc0 (abs_nonneg T)).2 hTlarge
      simpa only [sq_abs] using hs
    have hDlower : (q / 64) ^ 2 < D := by
      simp only [D]
      nlinarith [sq_nonneg q]
    have hD0 : 0 ≤ D := le_of_lt (lt_of_le_of_lt (sq_nonneg (q / 64)) hDlower)
    have hsqrtSq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD0
    have hsqrtLarge : q / 64 < Real.sqrt D := by
      exact (Real.lt_sqrt (by positivity)).2 hDlower
    let zplus : ℝ := (T + Real.sqrt D) / 2
    let zminus : ℝ := (T - Real.sqrt D) / 2
    refine ⟨zplus, zminus, ?_, ?_, ?_⟩
    · simp only [zplus, zminus]
      ring
    · simp only [zplus, zminus]
      calc
        (T + Real.sqrt D) / 2 * ((T - Real.sqrt D) / 2) =
            (T ^ 2 - (Real.sqrt D) ^ 2) / 4 := by ring
        _ = (T ^ 2 - D) / 4 := by rw [hsqrtSq]
        _ = A := by simp only [D]; ring
    · by_cases hT0 : 0 ≤ T
      · have habsT : |T| = T := abs_of_nonneg hT0
        have hzplusPos : 0 < zplus := by
          simp only [zplus]
          have hq64pos : 0 < q / 64 := div_pos hqpos (by norm_num)
          have hsqrtPos : 0 < Real.sqrt D := hq64pos.trans hsqrtLarge
          exact div_pos (add_pos_of_nonneg_of_pos hT0 hsqrtPos) (by norm_num)
        have hzplusLarge : q / 2 < |zplus| := by
          rw [abs_of_pos hzplusPos]
          simp only [zplus]
          rw [habsT] at hTlarge
          have hsum : q < T + Real.sqrt D := by
            calc
              q = 63 * q / 64 + q / 64 := by ring
              _ < T + Real.sqrt D := add_lt_add hTlarge hsqrtLarge
          exact (div_lt_div_iff_of_pos_right (by norm_num)).2 hsum
        exact lt_of_lt_of_le hzplusLarge (le_max_left _ _)
      · have hTneg : T < 0 := lt_of_not_ge hT0
        have habsT : |T| = -T := abs_of_neg hTneg
        have hzminusNeg : zminus < 0 := by
          simp only [zminus]
          have hnum : T - Real.sqrt D < 0 :=
            sub_neg.mpr (hTneg.trans_le (Real.sqrt_nonneg D))
          exact div_neg_of_neg_of_pos hnum (by norm_num)
        have hzminusLarge : q / 2 < |zminus| := by
          rw [abs_of_neg hzminusNeg]
          simp only [zminus]
          rw [habsT] at hTlarge
          have hsum : q < -T + Real.sqrt D := by
            calc
              q = 63 * q / 64 + q / 64 := by ring
              _ < -T + Real.sqrt D := add_lt_add hTlarge hsqrtLarge
          calc
            q / 2 < (-T + Real.sqrt D) / 2 :=
              (div_lt_div_iff_of_pos_right (by norm_num)).2 hsum
            _ = -((T - Real.sqrt D) / 2) := by ring
        exact lt_of_lt_of_le hzminusLarge (le_max_right _ _)


end Problem56.PaperV7
