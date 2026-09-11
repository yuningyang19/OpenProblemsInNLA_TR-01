import Problem56.PaperV7.SamplingPointwise
import Problem56.PaperV7.GeneralSamplingExpected

open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV7
open Problem56.PaperV6

theorem general_sampling : GeneralSamplingExpected := by
  intro Ω α _ _ _ μ _ r k X hX horth ε γ he0 he1 hk0 hkn hminus hplus
  have he : 0 < ε ∧ ε < 1 := ⟨he0, he1⟩
  have hk : 1 ≤ k ∧ k ≤ Fintype.card α := ⟨hk0, hkn⟩
  have hmtheta := sampling_theta_minus ε he hk
  by_cases hs : (1 + ε / 4) * k / Fintype.card α < 1
  · exact Problem56.PaperV6.general_sampling Ω α μ r k X hX horth ε γ
      he0 he1 hk0 hkn hmtheta.2 hs.le hminus (hplus hs)
  let θminus : ℝ := (1 - ε / 4) * k / Fintype.card α
  let F : Ω → ℝ := fun ω ↦ uniformProbability (fun J : FixedSubset α k ↦
    euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε)
  let B : Ω → ℝ := fun ω ↦ bernoulliProbability θminus (fun e ↦
    euclideanOperatorNorm (bernoulliGram θminus (X ω) e - 1) > ε / 4)
  let c : ℝ := Real.exp (-(ε ^ 2 * k / 48))
  have hF : Integrable F μ := integrable_fixed_failure μ X hX ε
  have hB : Integrable B μ := integrable_bernoulli_failure μ X hX θminus (ε / 4)
  have hb : ∫ ω, F ω ∂μ ≤ ∫ ω, (B ω + c) ∂μ := by
    apply integral_mono_ae hF (hB.add (integrable_const c))
    filter_upwards [horth] with ω hω
    exact sampling_pointwise_saturated (fun _ : Unit ↦ X ω) (fun _ ↦ hω)
      ε he hk (le_of_not_gt hs) ()
  rw [integral_add hB (integrable_const c)] at hb
  simp only [integral_const] at hb
  simp at hb
  have hnonneg : 0 ≤ ∫ ω, B ω ∂μ := by
    apply integral_nonneg
    intro ω
    classical
    unfold B bernoulliProbability
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact bernoulliWeight_nonneg _ hmtheta e
    · exact le_rfl
  change (∫ ω, B ω ∂μ) ≤ γ at hminus
  change (∫ ω, F ω ∂μ) ≤ 2 * γ + 2 * c
  have hc : 0 < c := Real.exp_pos _
  linarith
end Problem56.PaperV7
