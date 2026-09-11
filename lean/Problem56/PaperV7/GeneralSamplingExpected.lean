import Problem56.PaperV6.GeneralSamplingExpected
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV7
open Problem56.PaperV6
/-- General random-frame v7 sampling target, including the saturated upper branch. The hypotheses bound the
averaged marginal failure probabilities, not a pointwise maximum in ω. -/
def GeneralSamplingExpected : Prop :=
  ∀ (Ω α : Type) [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r k : ℕ)
    (X : Ω → Matrix α (Fin r) ℝ),
    Measurable (fun ω ↦ fun i j ↦ X ω i j) → (∀ᵐ ω ∂μ, OrthonormalFrame (X ω)) →
    ∀ (ε γ : ℝ), 0 < ε → ε < 1 →
    1 ≤ k → k ≤ Fintype.card α →
    averagedBernoulliFailureProbability μ
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ →
    ((1 + ε / 4) * k / Fintype.card α < 1 →
      averagedBernoulliFailureProbability μ
      ((1 + ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ) →
    averagedFixedFailureProbability (k := k) μ ε X ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48))

end Problem56.PaperV7
