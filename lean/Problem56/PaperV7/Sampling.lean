import Problem56.PaperV7.SamplingPointwise
open scoped BigOperators Matrix
namespace Problem56.PaperV7
private lemma uniformProbability_prod_eq_uniformExpectation
    {A B : Type*} [Fintype A] [Fintype B]
    (event : A × B → Prop) [DecidablePred event] :
    uniformProbability event =
      uniformExpectation (fun a ↦
        (∑ b, if event (a, b) then (1 : ℝ) else 0) /
          Fintype.card B) := by
  classical
  unfold uniformProbability uniformExpectation
  rw [Fintype.card_prod]
  rw [← Finset.sum_boole]
  rw [Fintype.sum_prod_type]
  push_cast
  simp_rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_inv]
  by_cases h : event (a, b)
  · simp [h, mul_comm]
  · simp [h]

private lemma uniformExpectation_mono
    {A : Type*} [Fintype A] (f g : A → ℝ)
    (hfg : ∀ a, f a ≤ g a) :
    uniformExpectation f ≤ uniformExpectation g := by
  unfold uniformExpectation
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun a _ ↦ hfg a
  · positivity

private lemma uniformExpectation_add
    {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformExpectation (fun a ↦ f a + g a) =
      uniformExpectation f + uniformExpectation g := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib]
  ring

private lemma uniformExpectation_const
    {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformExpectation (fun _ : A ↦ c) = c := by
  unfold uniformExpectation
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [Fintype.card_ne_zero]

theorem fixed_size_sampling_transfer_proof
    {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α] [DecidableEq α]
    {r k : ℕ} (X : Ω → Matrix α (Fin r) ℝ)
    (hX : ∀ ω, OrthonormalFrame (X ω))
    (ε γ : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hminus : uniformBernoulliFailureProbability
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ)
    (hplus : (1 + ε / 4) * k / Fintype.card α < 1 →
      uniformBernoulliFailureProbability
      ((1 + ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ) :
    uniformFixedFailureProbability (k := k) ε X ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48)) := by
  classical
  have hmtheta := sampling_theta_minus ε hε hk
  by_cases hs : (1 + ε / 4) * k / Fintype.card α < 1
  · exact Problem56.fixed_size_sampling_transfer_proof X hX ε γ hε hk
      hmtheta.2 hs.le hminus (hplus hs)
  · have hpoint := sampling_pointwise_saturated X hX ε hε hk (le_of_not_gt hs)
    have havg := uniformExpectation_mono _ _ hpoint
    rw [uniformExpectation_add, uniformExpectation_const] at havg
    have hfixed : uniformFixedFailureProbability (k := k) ε X =
        uniformExpectation (fun ω ↦ uniformProbability (fun J : FixedSubset α k ↦
          euclideanOperatorNorm (fixedSampleGram (X ω) J - 1) > ε)) := by
      unfold uniformFixedFailureProbability
      rw [uniformProbability_prod_eq_uniformExpectation]
      congr 1
      funext ω
      unfold uniformProbability
      rw [← Finset.sum_boole]
    rw [← hfixed] at havg
    change uniformFixedFailureProbability (k := k) ε X ≤
      uniformBernoulliFailureProbability ((1 - ε / 4) * k / Fintype.card α)
        (ε / 4) X + Real.exp (-(ε ^ 2 * k / 48)) at havg
    have hbnonneg : 0 ≤ uniformBernoulliFailureProbability
        ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X := by
      unfold uniformBernoulliFailureProbability uniformExpectation
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro ω _
      unfold bernoulliProbability
      apply Finset.sum_nonneg
      intro b _
      split_ifs
      · exact bernoulliWeight_nonneg _ hmtheta b
      · exact le_rfl
    have hexp := Real.exp_pos (-(ε ^ 2 * k / 48))
    linarith
end Problem56.PaperV7
