import Problem56.FinalWidth
namespace Problem56.PaperV7
theorem exp_neg_42_lt_one_div_250 :
    Real.exp (-42) < (1 : ℝ) / 250 := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (42 : ℝ)) (by norm_num) 3
  have h925 : (925 : ℝ) ≤ Real.exp 42 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
    exact hseries
  have h250 : (250 : ℝ) < Real.exp 42 := (by norm_num : (250 : ℝ) < 925).trans_le h925
  have hexp : 0 < Real.exp 42 := Real.exp_pos 42
  rw [Real.exp_neg, div_eq_mul_inv]
  apply (inv_lt_iff_one_lt_mul₀' hexp).2
  norm_num
  nlinarith

theorem exponential_remainder_lt (x : ℝ) (hx : 42 < x) :
    (2 : ℝ) / 1000 + 2 * Real.exp (-x) < 1 / 100 := by
  have hmono : Real.exp (-x) ≤ Real.exp (-42) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsmall : Real.exp (-x) < (1 : ℝ) / 250 :=
    hmono.trans_lt exp_neg_42_lt_one_div_250
  linarith

theorem rank_le_scaled_ceil (c r : ℕ) (ε : ℝ)
    (hc : 1 ≤ c) (hr : 1 ≤ r) (hε : 0 < ε ∧ ε < 1) :
    r ≤ Nat.ceil ((c : ℝ) * r / ε ^ 2) := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hεsq_le : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hscale : (r : ℝ) ≤ (c : ℝ) * r / ε ^ 2 := by
    apply (le_div_iff₀ hεsq).2
    nlinarith
  have hceil := Nat.le_ceil ((c : ℝ) * r / ε ^ 2)
  exact_mod_cast hscale.trans hceil


noncomputable def prescribedWidth (m r : ℕ) (ε : ℝ) : ℕ :=
  min (walshCard m) (Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2))
theorem prescribedWidth_bounds (m r : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hrn : r ≤ walshCard m) (hε : 0 < ε ∧ ε < 1) :
    r ≤ prescribedWidth m r ε ∧ prescribedWidth m r ε ≤ walshCard m := by
  refine ⟨le_min hrn ?_, Nat.min_le_left _ _⟩
  exact rank_le_scaled_ceil explicitUniversalConstant r ε
    (by norm_num [explicitUniversalConstant, R₀, K₀, K₂]) hr hε
theorem prescribedWidth_nonfull_lower (m r : ℕ) (ε : ℝ)
    (hfull : prescribedWidth m r ε ≠ walshCard m) :
    (explicitUniversalConstant : ℝ) * r / ε ^ 2 ≤ prescribedWidth m r ε := by
  have hlt : Nat.ceil ((explicitUniversalConstant : ℝ) * r / ε ^ 2) < walshCard m := by
    by_contra h
    apply hfull
    exact Nat.min_eq_left (Nat.le_of_not_gt h)
  rw [prescribedWidth, Nat.min_eq_right hlt.le]
  exact Nat.le_ceil _
theorem exact_width_effective (r k : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hk : (explicitUniversalConstant : ℝ) * r / ε ^ 2 ≤ k) :
    (1536 * K₀ : ℝ) * r / ε ^ 2 ≤ (3 : ℝ) / 4 * k := by
  have hC : (2048 : ℝ) * K₀ ≤ explicitUniversalConstant := by
    rw [explicitUniversalConstant]
    push_cast
    nlinarith [(Nat.cast_nonneg R₀ : (0 : ℝ) ≤ R₀), (Nat.cast_nonneg K₀ : (0 : ℝ) ≤ K₀)]
  have hbase : (2048 * K₀ : ℝ) * r / ε ^ 2 ≤ k := by
    apply le_trans _ hk
    gcongr
  calc
    (1536 * K₀ : ℝ) * r / ε ^ 2 =
        (3 : ℝ) / 4 * ((2048 * K₀ : ℝ) * r / ε ^ 2) := by ring
    _ ≤ (3 : ℝ) / 4 * k := mul_le_mul_of_nonneg_left hbase (by norm_num)
theorem exact_width_exponential_tail (r k : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hε : 0 < ε)
    (hk : (explicitUniversalConstant : ℝ) * r / ε ^ 2 ≤ k) :
    2 / 1000 + 2 * Real.exp (-(ε ^ 2 * k / 48)) < 1 / 100 := by
  apply exponential_remainder_lt
  have he := exact_width_effective r k ε hε hk
  have hs : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hscaled := (div_le_iff₀ hs).mp he
  have hK : (1 : ℝ) ≤ K₀ := by norm_num [K₀, K₂]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hKr : (1 : ℝ) ≤ (K₀ : ℝ) * r := by nlinarith
  nlinarith
theorem exact_width_small_rank_tail (r k : ℕ) (ε : ℝ)
    (hr : 1 ≤ r) (hsmall : r < R₀) (hkpos : 1 ≤ k) (hε : 0 < ε)
    (hk : (explicitUniversalConstant : ℝ) * r / ε ^ 2 ≤ k) :
    (r : ℝ) * (r + 1) / ((k : ℝ) * ε ^ 2) ≤ 1 / 100 := by
  have hs : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hscaled := (div_le_iff₀ hs).mp hk
  have hC : (200 : ℝ) * R₀ ≤ explicitUniversalConstant := by
    rw [explicitUniversalConstant]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (Nat.cast_nonneg K₀))
  have hrR : (r : ℝ) ≤ R₀ := by exact_mod_cast hsmall.le
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrplus : (r : ℝ) + 1 ≤ 2 * R₀ := by linarith
  have hbound : (100 : ℝ) * (r * (r + 1)) ≤ explicitUniversalConstant * r := by
    have hmul := mul_le_mul_of_nonneg_right hrplus (show (0 : ℝ) ≤ r by positivity)
    have hmulC := mul_le_mul_of_nonneg_right hC (show (0 : ℝ) ≤ r by positivity)
    nlinarith only [hmul, hmulC]
  apply (div_le_iff₀ (mul_pos hkR hs)).2
  nlinarith only [hbound, hscaled]
end Problem56.PaperV7
