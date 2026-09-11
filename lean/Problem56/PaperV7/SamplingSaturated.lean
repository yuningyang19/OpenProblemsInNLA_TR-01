import Problem56.PaperV7.SamplingHelpers
import Problem56.PaperV6.GeneralSampling

open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace Problem56.PaperV7

lemma sampling_theta_minus {α : Type*} [Fintype α] {k : ℕ}
    (ε : ℝ) (he : 0 < ε ∧ ε < 1) (hk : 1 ≤ k ∧ k ≤ Fintype.card α) :
    0 ≤ (1 - ε / 4) * k / Fintype.card α ∧
      (1 - ε / 4) * k / Fintype.card α ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast lt_of_lt_of_le hk.1 hk.2
  have hkn : (k : ℝ) ≤ Fintype.card α := by exact_mod_cast hk.2
  constructor
  · exact div_nonneg (mul_nonneg (by linarith [he.2]) (Nat.cast_nonneg k)) hn.le
  · apply (div_le_one hn).mpr
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma bernoulliProbability_one {α : Type*} [Fintype α] [DecidableEq α]
    (E : SignLayer α → Prop) [DecidablePred E] :
    bernoulliProbability 1 E = if E (fun _ ↦ true) then 1 else 0 := by
  classical
  have hw (b : SignLayer α) : bernoulliWeight 1 b = if b = (fun _ ↦ true) then 1 else 0 := by
    by_cases hb : b = (fun _ ↦ true)
    · simp [bernoulliWeight, hb]
    · have hex : ∃ i, b i = false := by
        by_contra h
        apply hb
        funext i
        have hi := not_exists.mp h i
        cases hbi : b i <;> simp_all
      obtain ⟨i, hi⟩ := hex
      have hz : bernoulliWeight 1 b = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
      simp [hb, hz]
  unfold bernoulliProbability
  simp_rw [hw]
  rw [Finset.sum_eq_single (fun _ ↦ true)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- A deterministic all-rows Gram comparison; q is an algebraic scale here,
not a Bernoulli probability in the saturated branch. -/
lemma saturated_full_gram {α : Type*} [Fintype α] [DecidableEq α] {r k : ℕ}
    (X : Matrix α (Fin r) ℝ) (hX : OrthonormalFrame X)
    (ε : ℝ) (he : 0 < ε ∧ ε < 1) (hk : 1 ≤ k ∧ k ≤ Fintype.card α)
    (hs : 1 ≤ (1 + ε / 4) * k / Fintype.card α) :
    euclideanOperatorNorm (bernoulliGram ((1 + ε / 4) * k / Fintype.card α)
      X (fun _ ↦ true) - 1) ≤ ε / 4 := by
  let q : ℝ := (1 + ε / 4) * k / Fintype.card α
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast lt_of_lt_of_le hk.1 hk.2
  have hkn : (k : ℝ) ≤ Fintype.card α := by exact_mod_cast hk.2
  have hq : q ≤ 1 + ε / 4 := by
    dsimp [q]
    apply (div_le_iff₀ hn).mpr
    exact mul_le_mul_of_nonneg_left hkn (by linarith [he.1])
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hs
  have hi : |q⁻¹ - 1| ≤ ε / 4 := by
    have hile : q⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hs
    rw [abs_of_nonpos (by linarith)]
    have hmul : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0.ne'
    have hp : 0 ≤ (ε / 4) * (q - 1) := mul_nonneg (by linarith [he.1]) (by linarith)
    nlinarith
  have hp : bernoulliProjection (fun _ : α ↦ true) = 1 := by
    simp [bernoulliProjection]
  have hg : bernoulliGram q X (fun _ ↦ true) - 1 = (q⁻¹ - 1) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    simp [bernoulliGram, hp, OrthonormalFrame] at hX ⊢
    rw [hX, sub_smul, one_smul]
  change euclideanOperatorNorm (bernoulliGram q X (fun _ ↦ true) - 1) ≤ ε / 4
  rw [hg, sampling_euclideanOperatorNorm_eq_l2_opNorm, norm_smul, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    have hone : (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := Subsingleton.elim _ _
    rw [hone, norm_zero, mul_zero]
    linarith [he.1]
  · letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
    simpa using hi

end Problem56.PaperV7
