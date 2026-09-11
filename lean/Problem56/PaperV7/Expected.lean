import Problem56.Definitions
import Problem56.PaperV6.GeneralSamplingExpected

/-! Independent v7 obligations, no proofs or axioms and no PaperV7 proof imports. -/
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory
namespace Problem56.PaperV7.Reference

def SpectralTransferExpected : Prop :=
  ∀
    {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ < 1),
    let A := (X * X.transpose - δ • 1) * (E - θ • 1)
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    Matrix.trace (A ^ (2 * p)) ≥ -2 * r * a2 ^ p ∧
      ∀ η : ℝ, 0 < η → η < 1 → δ ≤ θ * η ^ 2 / 64 →
        (if euclideanOperatorNorm (θ⁻¹ • (X.transpose * E * X) - 1) > η
          then (θ * η / 2) ^ (2 * p) else 0) ≤
          Matrix.trace (A ^ (2 * p)) + 2 * r * a2 ^ p

def SignedTraceExpected : Prop :=
  ∀ {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ : 0 < θ ∧ θ < 1)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r),
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace (((randomProjection d₁ d₂ V -
          ((r : ℝ) / walshCard m) • 1) *
        (bernoulliProjection e - θ • 1)) ^ (2 * p)))| ≤
      (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p

def BernoulliExpected : Prop :=
  ∀ {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (p : ℕ) (hp : p = Nat.ceil (Real.logb 2 (3000 * r : ℝ)))
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (η θ : ℝ) (hη : 0 < η ∧ η < 1) (hθ : 0 < θ ∧ θ < 1)
    (hκ : 64 * K₀ * r / η ^ 2 ≤ (walshCard m : ℝ) * θ),
    signPairExpectation (fun d₁ d₂ ↦
      bernoulliProbability θ (fun e ↦
        euclideanOperatorNorm
          (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η)) ≤
      1 / 1000

def MainPrescribedWidthExpected : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (m r : ℕ) (ε : ℝ),
    1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
    spectralFailureSup m r
      (min (walshCard m) (Nat.ceil (C * r / ε ^ 2))) ε ≤ 1 / 100

def ExplicitPrescribedWidthExpected : Prop :=
  1 ≤ explicitUniversalConstant ∧ ∀ (m r : ℕ) (ε : ℝ),
    1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
    spectralFailureSup m r
      (min (walshCard m) (Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2))) ε ≤ 1 / 100

def GeneralSamplingExpected : Prop :=
  ∀ (Ω α : Type) [MeasurableSpace Ω] [Fintype α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r k : ℕ)
    (X : Ω → Matrix α (Fin r) ℝ),
    Measurable (fun ω ↦ fun i j ↦ X ω i j) → (∀ᵐ ω ∂μ, OrthonormalFrame (X ω)) →
    ∀ (ε γ : ℝ), 0 < ε → ε < 1 → 0 ≤ γ →
    1 ≤ k → k ≤ Fintype.card α →
    PaperV6.averagedBernoulliFailureProbability μ
      ((1 - ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ →
    ((1 + ε / 4) * k / Fintype.card α < 1 →
      PaperV6.averagedBernoulliFailureProbability μ
        ((1 + ε / 4) * k / Fintype.card α) (ε / 4) X ≤ γ) →
    PaperV6.averagedFixedFailureProbability (k := k) μ ε X ≤
      2 * γ + 2 * Real.exp (-(ε ^ 2 * k / 48))

def SmallRankExpected : Prop :=
  ∀ {m r k : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ),
    OrthonormalFrame V → 1 ≤ k ∧ k ≤ walshCard m →
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k ∧
    (∀ ε : ℝ, 0 < ε →
      frameFailureProbability (k := k) ε V ≤ (r : ℝ) * (r + 1) / (k * ε ^ 2))

end Problem56.PaperV7.Reference
