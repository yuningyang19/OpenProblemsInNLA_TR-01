import Problem56.PaperV7.Results
import Problem56.PaperV7.ExactWidth
import Problem56.PaperV7.Sampling

namespace Problem56.PaperV7

theorem frame_failure_large_prescribed_width {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (ε : ℝ) (hr : 1 ≤ r) (hlarge : R₀ ≤ r)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hk : 1 ≤ k ∧ k ≤ walshCard m)
    (hlower : (explicitUniversalConstant : ℝ) * r / ε ^ 2 ≤ k) :
    frameFailureProbability (k := k) ε V ≤ 1 / 100 := by
  let X : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) →
      Matrix (WalshIndex m) (Fin r) ℝ :=
    fun d ↦ transformedFrame d.1 d.2 V
  let θminus : ℝ := (1 - ε / 4) * k / walshCard m
  let θplus : ℝ := (1 + ε / 4) * k / walshCard m
  have hnpos : (0 : ℝ) < walshCard m := by simp [walshCard]
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hη : 0 < ε / 4 ∧ ε / 4 < 1 := by
    constructor
    · nlinarith only [hε0]
    · nlinarith only [hε1]
  have hminusFactor : 0 < 1 - ε / 4 := by
    nlinarith only [hε1]
  have hplusFactor : 0 < 1 + ε / 4 := by
    nlinarith only [hε0]
  have hθminus0 : 0 < θminus := by
    exact div_pos (mul_pos hminusFactor hkposR) hnpos
  have hθplus0 : 0 < θplus := by
    exact div_pos (mul_pos hplusFactor hkposR) hnpos
  have hθminus1 : θminus < 1 := by
    apply (div_lt_iff₀ hnpos).2
    have hkn : (k : ℝ) ≤ walshCard m := by exact_mod_cast hk.2
    have hcut : (1 - ε / 4) * (k : ℝ) < k := by nlinarith only [hε0, hkposR]
    simpa only [one_mul] using hcut.trans_le hkn
  have hθorder : θminus ≤ θplus := by
    apply (div_le_div_iff_of_pos_right hnpos).2
    nlinarith only [hε0, hkposR]
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε0
  have hnθminus : (walshCard m : ℝ) * θminus =
      (1 - ε / 4) * k := by
    dsimp only [θminus]
    field_simp
  have hthreequarter : (3 : ℝ) / 4 * k ≤
      (walshCard m : ℝ) * θminus := by
    rw [hnθminus]
    nlinarith only [hε1, hkposR]
  have heffective' : (1536 * K₀ : ℝ) * r / ε ^ 2 ≤
      (3 : ℝ) / 4 * k := by
    exact exact_width_effective r k ε hε0 hlower
  have hwidthMinus : 64 * K₀ * r / (ε / 4) ^ 2 ≤
      (walshCard m : ℝ) * θminus := by
    calc
      64 * K₀ * r / (ε / 4) ^ 2 =
          1024 * K₀ * r / ε ^ 2 := by ring
      _ ≤ 1536 * K₀ * r / ε ^ 2 := by
        apply (div_le_div_iff_of_pos_right hεsq).2
        have hnonneg : 0 ≤ (K₀ : ℝ) * r :=
          mul_nonneg (Nat.cast_nonneg K₀) (Nat.cast_nonneg r)
        nlinarith only [hnonneg]
      _ ≤ (3 : ℝ) / 4 * k := heffective'
      _ ≤ (walshCard m : ℝ) * θminus := hthreequarter
  have hwidthPlus : 64 * K₀ * r / (ε / 4) ^ 2 ≤
      (walshCard m : ℝ) * θplus := by
    exact hwidthMinus.trans
      (mul_le_mul_of_nonneg_left hθorder hnpos.le)
  let p₀ : ℕ := Nat.ceil (Real.logb 2 (3000 * r : ℝ))
  have hp₀rank : 2 * (4 * p₀ + 1) ^ 1000 ≤ r := by
    simpa only [p₀] using I41_large_rank_cutoff_arithmetic r hlarge
  have hminusFail : uniformBernoulliFailureProbability
      θminus (ε / 4) X ≤ 1 / 1000 := by
    simpa only [uniformBernoulliFailureProbability, signPairExpectation,
      X] using
      (bernoulli_coordinate_sampling_corollary V hV p₀ rfl hp₀rank
        (ε / 4) θminus hη ⟨hθminus0, hθminus1⟩ hwidthMinus)
  have hplusFail : θplus < 1 → uniformBernoulliFailureProbability
      θplus (ε / 4) X ≤ 1 / 1000 := by
    intro ht
    simpa only [uniformBernoulliFailureProbability, signPairExpectation, X] using
      (bernoulli_coordinate_sampling_corollary V hV p₀ rfl hp₀rank
        (ε / 4) θplus hη ⟨hθplus0, ht⟩ hwidthPlus)
  have hX : ∀ d, OrthonormalFrame (X d) := by
    intro d
    exact transformedFrame_orthonormal V hV d.1 d.2
  rw [frameFailureProbability_eq_uniformFixed]
  have hfixed := fixed_size_sampling_transfer_proof X hX ε (1 / 1000)
    ⟨hε0, hε1⟩ hk hminusFail hplusFail
  exact hfixed.trans (by simpa only [show (2 : ℝ) * (1 / 1000) = 2 / 1000 by ring] using
    (exact_width_exponential_tail r k ε hr hε0 hlower).le)

/-- The exact prescribed-width OSE, with the supremum outside probability. -/
theorem main_prescribed_width_ose :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        let k := Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2))
        r ≤ k ∧ k ≤ walshCard m ∧ spectralFailureSup m r k ε ≤ 1 / 100 := by
  refine ⟨explicitUniversalConstant, rfl, ?_, ?_⟩
  · norm_num [explicitUniversalConstant, R₀, K₀, K₂]
  intro m r ε hr hrn hε0 hε1
  change r ≤ prescribedWidth m r ε ∧ prescribedWidth m r ε ≤ walshCard m ∧ _
  obtain ⟨hrk, hkn⟩ := prescribedWidth_bounds m r ε hr hrn ⟨hε0, hε1⟩
  refine ⟨hrk, hkn, ?_⟩
  apply Real.sSup_le
  · intro z hz
    obtain ⟨V, hV, rfl⟩ := hz
    by_cases hfull : prescribedWidth m r ε = walshCard m
    · change frameFailureProbability (k := prescribedWidth m r ε) ε V ≤ _
      rw [hfull, frameFailureProbability_full_sample V hV ε hε0]
      norm_num
    have hlower := prescribedWidth_nonfull_lower m r ε hfull
    have hk : 1 ≤ prescribedWidth m r ε ∧ prescribedWidth m r ε ≤ walshCard m :=
      ⟨hr.trans hrk, hkn⟩
    by_cases hsmall : r < R₀
    · exact (small_rank_failure_bound V hV hk ε hε0).trans
        (exact_width_small_rank_tail r _ ε hr hsmall hk.1 hε0 hlower)
    · exact frame_failure_large_prescribed_width V hV ε hr
        (Nat.le_of_not_gt hsmall) hε0 hε1 hk hlower
  · norm_num

end Problem56.PaperV7
