import Problem56.PaperV7.SamplingCoupling
import Problem56.FixedSizeSamplingTransfer
import Problem56.PaperV6.GeneralSamplingExpected

open scoped BigOperators Matrix

namespace Problem56.PaperV7

/- Helpers adapted from FixedSizeSamplingTransfer and PaperV6.SamplingPointwise.
The coupling transport now accepts arbitrary ordered densities in [0,1];
the count estimate retains only the lower tail needed in the saturated branch.
The original modules remain unchanged. -/
def transferTrueFinset {ι : Type*} [Fintype ι]
    (b : SignLayer ι) : Finset ι :=
  Finset.univ.filter fun i ↦ b i = true

def signLayerEquiv
    {ι κ : Type*} (e : ι ≃ κ) : SignLayer ι ≃ SignLayer κ where
  toFun b := fun j ↦ b (e.symm j)
  invFun b := fun i ↦ b (e i)
  left_inv b := by funext i; simp
  right_inv b := by funext j; simp

@[simp]
lemma signLayerEquiv_apply
    {ι κ : Type*} (e : ι ≃ κ) (b : SignLayer ι) (j : κ) :
    signLayerEquiv e b j = b (e.symm j) := rfl

def fixedSubsetEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) : FixedSubset ι k ≃ FixedSubset κ k :=
  e.finsetCongr.subtypeEquiv fun J ↦ by simp

@[simp]
lemma fixedSubsetEquiv_val
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) (J : FixedSubset ι k) :
    (fixedSubsetEquiv k e J).1 = J.1.map e.toEmbedding := rfl

def couplingSpaceEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) :
    (FixedSubset ι k × SignLayer ι × SignLayer ι) ≃
      (FixedSubset κ k × SignLayer κ × SignLayer κ) :=
  (fixedSubsetEquiv k e).prodCongr
    ((signLayerEquiv e).prodCongr (signLayerEquiv e))

@[simp]
lemma couplingSpaceEquiv_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ) (J : FixedSubset ι k)
    (bminus bplus : SignLayer ι) :
    couplingSpaceEquiv k e (J, bminus, bplus) =
      (fixedSubsetEquiv k e J, signLayerEquiv e bminus,
        signLayerEquiv e bplus) := rfl

lemma transferTrueFinset_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (b : SignLayer ι) :
    transferTrueFinset (signLayerEquiv e b) =
      (transferTrueFinset b).map e.toEmbedding := by
  ext j
  constructor
  · intro hj
    unfold transferTrueFinset at hj
    have hb : b (e.symm j) = true := (Finset.mem_filter.mp hj).2
    exact Finset.mem_map.mpr ⟨e.symm j,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    unfold transferTrueFinset at hi ⊢
    have hb : b i = true := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hb⟩

lemma bernoulliWeight_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (θ : ℝ) (e : ι ≃ κ) (b : SignLayer ι) :
    bernoulliWeight θ (signLayerEquiv e b) = bernoulliWeight θ b := by
  classical
  unfold bernoulliWeight
  exact Equiv.prod_comp e.symm (fun i ↦ if b i then θ else 1 - θ)

lemma sum_pair_equiv_transfer
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (eA : A ≃ B) (eC : C ≃ D) (F : B → D → ℝ) :
    (∑ a, ∑ c, F (eA a) (eC c)) = ∑ b, ∑ d, F b d := by
  calc
    _ = ∑ a, ∑ d, F (eA a) d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eC (fun d ↦ F (eA a) d)
    _ = _ := Equiv.sum_comp eA (fun b ↦ ∑ d, F b d)

lemma coupling_support_of_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (e : ι ≃ κ)
    (sample : FixedSubset ι k × SignLayer ι × SignLayer ι)
    (hsupport :
      (∀ j, (signLayerEquiv e sample.2.1) j = true →
        (signLayerEquiv e sample.2.2) j = true) ∧
      (((transferTrueFinset (signLayerEquiv e sample.2.1)).card ≤ k ∧
          k ≤ (transferTrueFinset (signLayerEquiv e sample.2.2)).card) →
        (∀ j, (signLayerEquiv e sample.2.1) j = true →
          j ∈ (fixedSubsetEquiv k e sample.1).1) ∧
        (∀ j, j ∈ (fixedSubsetEquiv k e sample.1).1 →
          (signLayerEquiv e sample.2.2) j = true))) :
    (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
      (((transferTrueFinset sample.2.1).card ≤ k ∧
          k ≤ (transferTrueFinset sample.2.2).card) →
        (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
        (∀ i, i ∈ sample.1.1 → sample.2.2 i = true)) := by
  constructor
  · intro i hi
    have hm : (signLayerEquiv e sample.2.1) (e i) = true := by simpa
    have hp := hsupport.1 (e i) hm
    simpa using hp
  · intro hbracket
    have hbracket' :
        (transferTrueFinset (signLayerEquiv e sample.2.1)).card ≤ k ∧
          k ≤ (transferTrueFinset (signLayerEquiv e sample.2.2)).card := by
      simp only [transferTrueFinset_equiv, Finset.card_map]
      exact hbracket
    obtain ⟨hm, hp⟩ := hsupport.2 hbracket'
    constructor
    · intro i hi
      have hmapped := hm (e i) (by simpa)
      simpa using hmapped
    · intro i hi
      have hmapped : e i ∈ (fixedSubsetEquiv k e sample.1).1 := by
        simp [hi]
      have hp' := hp (e i) hmapped
      simpa using hp'

theorem uniform_key_nested_coupling_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (θminus θplus : ℝ) (hk : k ≤ Fintype.card ι)
    (hm : 0 ≤ θminus) (hle : θminus ≤ θplus) (hp : θplus ≤ 1) :
    ∃ coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ,
      (∀ sample, 0 ≤ coupling sample) ∧
      (∑ sample, coupling sample) = 1 ∧
      (∀ sample, coupling sample ≠ 0 →
        (∀ i, sample.2.1 i = true → sample.2.2 i = true) ∧
        (((transferTrueFinset sample.2.1).card ≤ k ∧
            k ≤ (transferTrueFinset sample.2.2).card) →
          (∀ i, sample.2.1 i = true → i ∈ sample.1.1) ∧
          (∀ i, i ∈ sample.1.1 → sample.2.2 i = true))) ∧
      (∀ J, (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset ι k)) ∧
      (∀ bminus, (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
        bernoulliWeight θminus bminus) ∧
      (∀ bplus, (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
        bernoulliWeight θplus bplus) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  obtain ⟨couplingFin, hnonneg, htotal, hsupport, hfixed, hminus, hplus⟩ :=
    sampling_nested_coupling n k θminus θplus (by simpa [n] using hk) hm hle hp
  let coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ :=
    fun sample ↦ couplingFin (couplingSpaceEquiv k e sample)
  refine ⟨coupling, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample
    exact hnonneg _
  · exact Equiv.sum_comp (couplingSpaceEquiv k e) couplingFin |>.trans htotal
  · intro sample hs
    rcases sample with ⟨J, bminus, bplus⟩
    apply coupling_support_of_equiv k e (J, bminus, bplus)
    have hsFin := hsupport (couplingSpaceEquiv k e (J, bminus, bplus)) hs
    simp only [couplingSpaceEquiv_apply] at hsFin
    refine ⟨hsFin.1, ?_⟩
    intro hbracket
    apply hsFin.2
    unfold transferTrueFinset at hbracket
    exact hbracket
  · intro J
    calc
      (∑ bminus, ∑ bplus, coupling (J, bminus, bplus)) =
          ∑ bminusFin, ∑ bplusFin,
            couplingFin (fixedSubsetEquiv k e J, bminusFin, bplusFin) := by
        exact sum_pair_equiv_transfer (signLayerEquiv e) (signLayerEquiv e)
          (fun bminusFin bplusFin ↦
            couplingFin (fixedSubsetEquiv k e J, bminusFin, bplusFin))
      _ = 1 / Fintype.card (FixedSubset (Fin n) k) := hfixed _
      _ = 1 / Fintype.card (FixedSubset ι k) := by
        congr 2
        exact Fintype.card_congr (fixedSubsetEquiv k e).symm
  · intro bminus
    calc
      (∑ J, ∑ bplus, coupling (J, bminus, bplus)) =
          ∑ JFin, ∑ bplusFin,
            couplingFin (JFin, signLayerEquiv e bminus, bplusFin) := by
        exact sum_pair_equiv_transfer (fixedSubsetEquiv k e) (signLayerEquiv e)
          (fun JFin bplusFin ↦
            couplingFin (JFin, signLayerEquiv e bminus, bplusFin))
      _ = bernoulliWeight θminus (signLayerEquiv e bminus) :=
        hminus _
      _ = bernoulliWeight θminus bminus := by
        simpa [n] using bernoulliWeight_equiv
          θminus e bminus
  · intro bplus
    calc
      (∑ J, ∑ bminus, coupling (J, bminus, bplus)) =
          ∑ JFin, ∑ bminusFin,
            couplingFin (JFin, bminusFin, signLayerEquiv e bplus) := by
        exact sum_pair_equiv_transfer (fixedSubsetEquiv k e) (signLayerEquiv e)
          (fun JFin bminusFin ↦
            couplingFin (JFin, bminusFin, signLayerEquiv e bplus))
      _ = bernoulliWeight θplus (signLayerEquiv e bplus) :=
        hplus _
      _ = bernoulliWeight θplus bplus := by
        simpa [n] using bernoulliWeight_equiv
          θplus e bplus

lemma weighted_fixed_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hfixed : ∀ J, (∑ bminus, ∑ bplus,
      coupling (J, bminus, bplus)) =
        1 / Fintype.card (FixedSubset ι k))
    (f : FixedSubset ι k → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f J) =
      ∑ J, (1 / Fintype.card (FixedSubset ι k)) * f J := by
  apply Finset.sum_congr rfl
  intro J _
  calc
    _ = (∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus)) * f J := by
      simp_rw [Finset.sum_mul]
    _ = _ := by rw [hfixed J]

lemma weighted_minus_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (θ : ℝ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hminus : ∀ bminus, (∑ J, ∑ bplus,
      coupling (J, bminus, bplus)) = bernoulliWeight θ bminus)
    (f : SignLayer ι → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f bminus) =
      ∑ bminus, bernoulliWeight θ bminus * f bminus := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bminus _
  calc
    _ = (∑ J, ∑ bplus,
        coupling (J, bminus, bplus)) * f bminus := by
      simp_rw [Finset.sum_mul]
    _ = _ := by rw [hminus bminus]

lemma weighted_plus_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (θ : ℝ)
    (coupling : FixedSubset ι k × SignLayer ι × SignLayer ι → ℝ)
    (hplus : ∀ bplus, (∑ J, ∑ bminus,
      coupling (J, bminus, bplus)) = bernoulliWeight θ bplus)
    (f : SignLayer ι → ℝ) :
    (∑ J, ∑ bminus, ∑ bplus,
        coupling (J, bminus, bplus) * f bplus) =
      ∑ bplus, bernoulliWeight θ bplus * f bplus := by
  calc
    _ = ∑ J, ∑ bplus, ∑ bminus,
        coupling (J, bminus, bplus) * f bplus := by
      apply Finset.sum_congr rfl
      intro J _
      rw [Finset.sum_comm]
    _ = ∑ bplus, ∑ J, ∑ bminus,
        coupling (J, bminus, bplus) * f bplus := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro bplus _
      calc
        _ = (∑ J, ∑ bminus,
            coupling (J, bminus, bplus)) * f bplus := by
          simp_rw [Finset.sum_mul]
        _ = _ := by rw [hplus bplus]

lemma bernoulliProbability_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (θ : ℝ) (event : SignLayer κ → Prop) :
    bernoulliProbability θ (fun b ↦ event (signLayerEquiv e b)) =
      bernoulliProbability θ event := by
  classical
  unfold bernoulliProbability
  calc
    (∑ b, if event (signLayerEquiv e b)
        then bernoulliWeight θ b else 0) =
        ∑ b, if event (signLayerEquiv e b)
          then bernoulliWeight θ (signLayerEquiv e b) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [bernoulliWeight_equiv θ e b]
    _ = _ := Equiv.sum_comp (signLayerEquiv e)
      (fun b ↦ if event b then bernoulliWeight θ b else 0)

theorem binomial_tail_bounds_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ a : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (ha : 0 ≤ a) :
    let μ := Fintype.card ι * θ
    bernoulliProbability θ (fun b : SignLayer ι ↦
      a ≤ ((transferTrueFinset b).card : ℝ) - μ) ≤
        Real.exp (-(a ^ 2) / (2 * μ + 2 * a / 3)) ∧
    bernoulliProbability θ (fun b : SignLayer ι ↦
      a ≤ μ - ((transferTrueFinset b).card : ℝ)) ≤
        Real.exp (-(a ^ 2) / (2 * μ)) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  have htail := binomial_tail_bounds n θ a hθ ha
  dsimp only at htail ⊢
  constructor
  · calc
      bernoulliProbability θ (fun b : SignLayer ι ↦
          a ≤ ((transferTrueFinset b).card : ℝ) -
            (Fintype.card ι : ℝ) * θ) =
          bernoulliProbability θ (fun b : SignLayer (Fin n) ↦
            a ≤ ((transferTrueFinset b).card : ℝ) - (n : ℝ) * θ) := by
        rw [← bernoulliProbability_equiv e θ]
        congr 1
        funext b
        rw [transferTrueFinset_equiv, Finset.card_map]
      _ ≤ _ := htail.1
  · calc
      bernoulliProbability θ (fun b : SignLayer ι ↦
          a ≤ (Fintype.card ι : ℝ) * θ -
            ((transferTrueFinset b).card : ℝ)) =
          bernoulliProbability θ (fun b : SignLayer (Fin n) ↦
            a ≤ (n : ℝ) * θ - ((transferTrueFinset b).card : ℝ)) := by
        rw [← bernoulliProbability_equiv e θ]
        congr 1
        funext b
        rw [transferTrueFinset_equiv, Finset.card_map]
      _ ≤ _ := htail.2

lemma bernoulliProbability_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (p q : SignLayer ι → Prop) (hpq : ∀ b, p b → q b) :
    bernoulliProbability θ p ≤ bernoulliProbability θ q := by
  classical
  unfold bernoulliProbability
  apply Finset.sum_le_sum
  intro b _
  by_cases hp : p b
  · simp [hp, hpq b hp]
  · by_cases hq : q b
    · simp [hp, hq, bernoulliWeight_nonneg θ hθ b]
    · simp [hp, hq]

theorem sampling_lower_count_tail_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (hk : 1 ≤ k ∧ k ≤ Fintype.card ι)
    (hthetaMinus : (1 - ε / 4) * k / Fintype.card ι ≤ 1)
 :
    bernoulliProbability ((1 - ε / 4) * k / Fintype.card ι)
        (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          Real.exp (-(ε ^ 2 * k / 48)) := by
  classical
  let θminus : ℝ := (1 - ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let θplus : ℝ := (1 + ε / 4) * (k : ℝ) /
    (Fintype.card ι : ℝ)
  let a : ℝ := (ε / 4) * (k : ℝ)
  let μminus : ℝ := (Fintype.card ι : ℝ) * θminus
  let μplus : ℝ := (Fintype.card ι : ℝ) * θplus
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk.1
  have hcardNat : 0 < Fintype.card ι := lt_of_lt_of_le hk.1 hk.2
  have hcardReal : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  have hθminus : 0 ≤ θminus ∧ θminus ≤ 1 := by
    constructor
    · dsimp [θminus]
      exact div_nonneg
        (mul_nonneg (by linarith [hε.2]) (Nat.cast_nonneg k))
        hcardReal.le
    · simpa [θminus] using hthetaMinus
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by linarith [hε.1]) (Nat.cast_nonneg k)
  have hμminus : μminus = (1 - ε / 4) * (k : ℝ) := by
    dsimp [μminus, θminus]
    field_simp
  have hμplus : μplus = (1 + ε / 4) * (k : ℝ) := by
    dsimp [μplus, θplus]
    field_simp
  have htailMinus := binomial_tail_bounds_fintype
    (ι := ι) θminus a hθminus ha
  dsimp only at htailMinus
  calc
      bernoulliProbability θminus
          (fun b : SignLayer ι ↦ k < (transferTrueFinset b).card) ≤
          bernoulliProbability θminus (fun b : SignLayer ι ↦
            a ≤ ((transferTrueFinset b).card : ℝ) - μminus) := by
        apply bernoulliProbability_mono θminus hθminus
        intro b hb
        have hbReal : (k : ℝ) < ((transferTrueFinset b).card : ℝ) := by
          exact_mod_cast hb
        dsimp [a]
        rw [hμminus]
        linarith
      _ ≤ Real.exp (-(a ^ 2) /
          (2 * μminus + 2 * a / 3)) := htailMinus.1
      _ ≤ Real.exp (-(ε ^ 2 * k / 48)) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 2 * μminus + 2 * a / 3 := by
          rw [hμminus]
          dsimp [a]
          have hfac : 0 < 1 - ε / 4 := by linarith
          have haPos : 0 < ε / 4 * (k : ℝ) :=
            mul_pos (by linarith) hkReal
          positivity
        have hratio : ε ^ 2 * (k : ℝ) / 48 ≤
            a ^ 2 / (2 * μminus + 2 * a / 3) := by
          rw [le_div_iff₀ hden]
          rw [hμminus]
          dsimp [a]
          field_simp
          nlinarith [sq_pos_of_pos hε.1, sq_pos_of_pos hkReal]
        simpa only [neg_div] using neg_le_neg hratio

end Problem56.PaperV7
