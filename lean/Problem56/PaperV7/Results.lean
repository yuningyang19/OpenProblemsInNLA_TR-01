import Problem56.Statements
import Problem56.PaperV7.SignedTraceExpansion
import Problem56.PaperV7.BernoulliSamplingCorollary

namespace Problem56.PaperV7

theorem signed_trace_proposition {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ : 0 < θ ∧ θ < 1)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace (((randomProjection d₁ d₂ V -
          ((r : ℝ) / walshCard m) • 1) *
        (bernoulliProjection e - θ • 1)) ^ (2 * p)))| ≤
      (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p := by
  apply signedTrace_bound
  · intro ι ε _ _ _ dim src dst M w r hconn heven hpositive hnorm hweight hrank
    exact graph_rank_contraction dim src dst M w r hconn heven hpositive hnorm
      hweight hrank
  · intro p s t hp
    exact (selector_equality_graph_count p s t hp).2
  · exact hV
  · exact hp
  · exact hθ.1
  · exact hθ.2
  · exact hκ
  · exact hr

theorem two_projection_spectral_transfer
    {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ < 1) :
    let A := (X * X.transpose - δ • 1) * (E - θ • 1)
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    Matrix.trace (A ^ (2 * p)) ≥ -2 * r * a2 ^ p ∧
      ∀ η : ℝ, 0 < η → η < 1 → δ ≤ θ * η ^ 2 / 64 →
        (if euclideanOperatorNorm (θ⁻¹ • (X.transpose * E * X) - 1) > η
          then (θ * η / 2) ^ (2 * p) else 0) ≤
          Matrix.trace (A ^ (2 * p)) + 2 * r * a2 ^ p := by
  exact two_projection_spectral_transfer_proof X E hX hE δ θ hp hδ hθ

theorem bernoulli_coordinate_sampling_corollary {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (p : ℕ) (hp : p = Nat.ceil (Real.logb 2 (3000 * r : ℝ)))
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (η θ : ℝ) (hη : 0 < η ∧ η < 1) (hθ : 0 < θ ∧ θ < 1)
    (hκ : 64 * K₀ * r / η ^ 2 ≤ (walshCard m : ℝ) * θ) :
    signPairExpectation (fun d₁ d₂ ↦
      bernoulliProbability θ (fun e ↦
        euclideanOperatorNorm
          (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η)) ≤
      1 / 1000 := by
  have hr2 : 2 ≤ r := by
    have hbasepos : 0 < (4 * p + 1) ^ 1000 :=
      pow_pos (by omega) 1000
    have hbase : 1 ≤ (4 * p + 1) ^ 1000 := hbasepos
    omega
  have hp2 : 2 ≤ p := by
    rw [hp]
    have hlog : (2 : ℝ) ≤ Real.logb 2 (3000 * r : ℝ) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).2
      rw [Real.rpow_two]
      norm_num
      exact_mod_cast (show 4 ≤ 3000 * r by omega)
    have hceil := hlog.trans (Nat.le_ceil (Real.logb 2 (3000 * r : ℝ)))
    exact_mod_cast hceil
  have hηsqpos : 0 < η ^ 2 := sq_pos_of_pos hη.1
  have hκ' : (64 : ℝ) * K₀ * r ≤
      ((walshCard m : ℝ) * θ) * η ^ 2 := by
    exact (div_le_iff₀ hηsqpos).mp (by simpa using hκ)
  have hηsqle : η ^ 2 ≤ 1 := by nlinarith [sq_nonneg η]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
  have hκtrace : (r : ℝ) ≤ (walshCard m : ℝ) * θ := by
    have hfactor : (1 : ℝ) ≤ 64 * K₀ := by nlinarith
    have hscale : (r : ℝ) ≤ 64 * K₀ * r := by
      calc
        (r : ℝ) = 1 * r := by ring
        _ ≤ (64 * K₀) * r := mul_le_mul_of_nonneg_right hfactor hrpos.le
    have hnθ : 0 ≤ (walshCard m : ℝ) * θ :=
      mul_nonneg (Nat.cast_nonneg _) hθ.1.le
    calc
      (r : ℝ) ≤ 64 * K₀ * r := hscale
      _ ≤ ((walshCard m : ℝ) * θ) * η ^ 2 := hκ'
      _ ≤ (walshCard m : ℝ) * θ :=
        mul_le_of_le_one_right hnθ hηsqle
  apply bernoulli_coordinate_sampling_corollary_of_trace
    V hV p hp hr η θ hη hθ hκ
  exact signed_trace_proposition V hV θ hp2 hθ hκtrace hr

theorem uniformProbability_prod_assoc
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (event : A × (B × C) → Prop) :
    uniformProbability event =
      uniformProbability (fun z : (A × B) × C ↦ event (z.1.1, z.1.2, z.2)) := by
  classical
  unfold uniformProbability
  let e : (A × B) × C ≃ A × (B × C) := Equiv.prodAssoc A B C
  have hnum :
      (∑ z : A × (B × C), if event z then (1 : ℝ) else 0) =
        ∑ z : (A × B) × C,
          if event (z.1.1, z.1.2, z.2) then (1 : ℝ) else 0 := by
    symm
    exact Fintype.sum_equiv e _ _ (fun z ↦ rfl)
  simp only [Finset.natCast_card_filter, Finset.sum_filter,
    Finset.mem_univ, if_true] at *
  rw [hnum]
  congr 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

theorem frameFailureProbability_eq_uniformFixed
    {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) :
    frameFailureProbability (k := k) ε V =
      uniformFixedFailureProbability (k := k) ε
        (fun d : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ↦
          transformedFrame d.1 d.2 V) := by
  unfold frameFailureProbability uniformFixedFailureProbability
  rw [uniformProbability_prod_assoc (A := SignLayer (WalshIndex m))
    (B := SignLayer (WalshIndex m)) (C := FixedSubset (WalshIndex m) k)]
  congr 1
  funext sample
  rw [I02_exact_gram_reduction]
  rfl

theorem frameFailureProbability_full_sample
    {m r : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (ε : ℝ) (hε : 0 < ε) :
    frameFailureProbability (k := walshCard m) ε V = 0 := by
  classical
  unfold frameFailureProbability uniformProbability
  have hpoint : ∀ sample : SignLayer (WalshIndex m) ×
      (SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) (walshCard m)),
      ¬ euclideanOperatorNorm
        (compressedGram V sample.1 sample.2.1 sample.2.2 - 1) > ε := by
    intro sample
    rw [I03_full_sample_exact V hV]
    simp only [sub_self]
    rw [euclideanOperatorNorm_eq_l2_opNorm]
    rw [Matrix.l2_opNorm_def]
    simpa using hε.le
  have hempty : (Finset.univ.filter fun sample : SignLayer (WalshIndex m) ×
      (SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) (walshCard m)) ↦
        euclideanOperatorNorm
          (compressedGram V sample.1 sample.2.1 sample.2.2 - 1) > ε) = ∅ := by
    ext sample
    simp [hpoint sample]
  rw [hempty]
  simp


theorem small_rank_failure_bound {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (hk : 1 ≤ k ∧ k ≤ walshCard m) (ε : ℝ) (hε : 0 < ε) :
    frameFailureProbability (k := k) ε V ≤
      (r : ℝ) * (r + 1) / ((k : ℝ) * ε ^ 2) := by
  classical
  obtain ⟨J₀, _, hJ₀⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (WalshIndex m)))
      (by simpa only [Finset.card_univ, walshCard] using hk.2)
  letI : Nonempty (FixedSubset (WalshIndex m) k) := ⟨⟨J₀, hJ₀⟩⟩
  have hprob : frameFailureProbability (k := k) ε V =
      uniformProbability
        (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
            FixedSubset (WalshIndex m) k ↦ euclideanOperatorNorm
          (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1) > ε) := by
    unfold frameFailureProbability
    congr 1
    funext sample
    rw [I02_exact_gram_reduction]
    rfl
  rw [hprob]
  have hmarkov := uniformProbability_operatorNorm_gt_le_frobeniusExpectation
    (fun sample : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k ↦
      fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)
    ε ((r : ℝ) * (r + 1) / k) hε
    (small_rank_frobenius_expectation_bound V hV hk)
  simpa only [div_div] using hmarkov

theorem small_rank_second_moment {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (hk : 1 ≤ k ∧ k ≤ walshCard m) :
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k ∧
    (∀ ε : ℝ, 0 < ε → frameFailureProbability (k := k) ε V ≤
      (r : ℝ) * (r + 1) / ((k : ℝ) * ε ^ 2)) :=
  ⟨small_rank_frobenius_expectation_bound V hV hk, small_rank_failure_bound V hV hk⟩
end Problem56.PaperV7
