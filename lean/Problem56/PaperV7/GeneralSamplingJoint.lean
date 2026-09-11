import Problem56.PaperV7.GeneralSampling
import Problem56.PaperV7.GeneralSamplingJointExpected
import Problem56.PaperV6.GeneralSamplingJoint
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV7
open Problem56.PaperV6

theorem general_sampling_joint : GeneralSamplingJointExpected := by
  intro Ω α _ _ _ μ _ r k _ _ _ _ X S Eminus Eplus ε γ hX horth hS hEm hEp hiS hiEm hiEp
    hε0 hε1 hk0 hkn
  dsimp only
  intro hSMarg hEmMarg hEpMarg hminus hplus
  have htminus := sampling_theta_minus ε ⟨hε0,hε1⟩ ⟨hk0,hkn⟩
  rw [bernoulli_noise_failure_law μ X Eminus hX hEm hiEm _ _ htminus hEmMarg] at hminus
  rw [fixed_noise_failure_law μ X S hX hS hiS hkn ε hSMarg]
  apply Problem56.PaperV7.general_sampling Ω α μ r k X hX horth ε γ
    hε0 hε1 hk0 hkn hminus
  intro hs
  have hp0 : 0 ≤ (1 + ε / 4) * (k : ℝ) / Fintype.card α := by positivity
  have h := hplus hs
  rw [bernoulli_noise_failure_law μ X Eplus hX (hEp hs) (hiEp hs) _ _ ⟨hp0,hs.le⟩ (hEpMarg hs)] at h
  exact h
/-- Saturated joint realization: there is no upper-draw parameter or hypothesis. -/
theorem general_sampling_joint_saturated
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
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48)) := by
  rw [bernoulli_noise_failure_law μ X Eminus hX hEm hiEm _ _
    (sampling_theta_minus ε he hk) hEmMarg] at hminus
  rw [fixed_noise_failure_law μ X S hX hS hiS hk.2 ε hSMarg]
  apply Problem56.PaperV7.general_sampling Ω α μ r k X hX horth ε γ
    he.1 he.2 hk.1 hk.2 hminus
  intro hlt
  exact False.elim (not_lt_of_ge hs hlt)

end Problem56.PaperV7
