import Problem56.PaperV6.EntryBridges

open scoped BigOperators Matrix Classical
namespace Problem56.PaperV7
open Problem56.PaperV6

theorem centeredBernoulliMomentVarianceBound
    (theta : ℝ) (b : ℕ) (hzero : 0 < theta)
    (hone : theta < 1) (hb : 2 ≤ b) :
    |theta * (1 - theta) ^ b + (1 - theta) * (-theta) ^ b| ≤ theta * (1 - theta) := by
  have htheta : 0 ≤ theta := hzero.le
  have hthetale : theta ≤ 1 := by linarith
  have honeneg : 0 ≤ 1 - theta := by linarith
  have honele : 1 - theta ≤ 1 := by linarith
  have hptheta : theta ^ b ≤ theta ^ 2 :=
    pow_le_pow_of_le_one htheta hthetale hb
  have hpone : (1 - theta) ^ b ≤ (1 - theta) ^ 2 :=
    pow_le_pow_of_le_one honeneg honele hb
  calc
    |theta * (1 - theta) ^ b + (1 - theta) * (-theta) ^ b| ≤
        |theta * (1 - theta) ^ b| +
          |(1 - theta) * (-theta) ^ b| := abs_add_le _ _
    _ = theta * (1 - theta) ^ b + (1 - theta) * theta ^ b := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_of_nonneg htheta, abs_of_nonneg honeneg, abs_neg]
    _ ≤ theta * (1 - theta) ^ 2 + (1 - theta) * theta ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpone htheta)
        (mul_le_mul_of_nonneg_left hptheta honeneg)
    _ = theta * (1 - theta) := by ring

theorem paperSelectorCoefficient_abs_le {p s t : ℕ}
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (Q : SelectorEqualityData p s t) :
    |paperSelectorCoefficient θ Q| ≤ θ ^ (p - s) := by
  classical
  unfold paperSelectorCoefficient
  rw [Finset.abs_prod]
  calc
    (∏ B ∈ Q.1.parts, |θ * (1 - θ) ^ B.card + (1 - θ) * (-θ) ^ B.card|) ≤
      ∏ _B ∈ Q.1.parts, θ := by
        apply Finset.prod_le_prod
        · intro B hB
          exact abs_nonneg _
        · intro B hB
          exact (centeredBernoulliMomentVarianceBound θ B.card hθ hθ' (Q.2.1 B hB)).trans (by nlinarith)
    _ = θ ^ (p - s) := by rw [Finset.prod_const, Q.2.2.1]

def EntryAbsoluteContributionExpected : Prop :=
  ∀ (m r p s t : ℕ), 2 ≤ p → 1 ≤ r →
    ∀ (V : Matrix (WalshIndex m) (Fin r) ℝ), OrthonormalFrame V →
    ∀ (θ : ℝ), 0 < θ → θ < 1 →
    ∀ (Q : SelectorEqualityData p s t) (d h : ℕ),
    paperEntryAbsoluteContribution V θ Q d h ≤
      ((3 * K₂ : ℕ) : ℝ) ^ p *
      ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) *
      (((r : ℝ) / walshCard m) * θ) ^ p *
      (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) * (walshCard m : ℝ) ^ (-(h : ℤ)))

theorem entry_absolute_contribution : EntryAbsoluteContributionExpected := by
  classical
  intro m r p s t hp hr V hV θ hθ hθ' Q d h
  by_cases hn : Nonempty (AggregateEntryPartition Q d h)
  · obtain ⟨A⟩ := hn
    obtain ⟨hd, hsh⟩ := aggregate_parameters hp A
    have hsum := paperEntry_fixed_class_sum_bound V hV Q (d := d) (h := h)
    have hcoeff := paperSelectorCoefficient_abs_le θ hθ hθ' Q
    have haggNat := (entry_weighted_count p s t hp Q d h).1
    have hagg : (aggregateEntryPartitionCumulantSum Q d h : ℝ) ≤
        ((3 * K₂ : ℕ) : ℝ) ^ p *
          ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) := by
      exact_mod_cast haggNat
    have hdim := paper_dimension_factor
      (walshCard m) r p s d h θ Fintype.card_pos (by omega) hθ (by omega) hsh
    let dim : ℝ := θ ^ (p - s) * (walshCard m : ℝ) ^ (p - s - h) *
      ((walshCard m : ℝ)⁻¹) ^ (2 * p) * (r : ℝ) ^ (p - d)
    have hdimnonneg : 0 ≤ dim := by dsimp [dim]; positivity
    calc
      paperEntryAbsoluteContribution V θ Q d h ≤
        θ ^ (p - s) * ((walshCard m : ℝ) ^ (p - s - h) *
          ((walshCard m : ℝ)⁻¹) ^ (2 * p) *
          (aggregateEntryPartitionCumulantSum Q d h : ℝ) * (r : ℝ) ^ (p - d)) := by
        exact mul_le_mul hcoeff hsum (by positivity) (by positivity)
      _ = dim * (aggregateEntryPartitionCumulantSum Q d h : ℝ) := by dsimp [dim]; ring
      _ ≤ dim * (((3 * K₂ : ℕ) : ℝ) ^ p *
          ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1)) :=
        mul_le_mul_of_nonneg_left hagg hdimnonneg
      _ = _ := by dsimp only [dim]; rw [hdim]; ring
  · haveI : IsEmpty (AggregateEntryPartition Q d h) := not_nonempty_iff.mp hn
    simp only [paperEntryAbsoluteContribution, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    positivity


end Problem56.PaperV7
