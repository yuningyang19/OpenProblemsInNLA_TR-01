import Problem56.TwoProjectionTransfer
import Problem56.PaperV7.SpectralRoot

/-! Full-density version of manuscript v7, Lemma 2, reusing the v6 block calculus. -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56.PaperV7

theorem exists_twoProjection_bad_block_trace_gt
    {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ η : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ < 1)
    (hη : 0 < η ∧ η < 1) (hsmall : δ ≤ θ * η ^ 2 / 64)
    (i : Fin r) (hbad : |compressionEigenvalue X E hE i - θ| > θ * η) :
    ∃ (Q : Matrix α α ℝ) (block : α → α) (b₀ : α),
      IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block ∧
      ((Finset.univ : Finset α).filter (fun k ↦
        ((Finset.univ : Finset α).filter fun j ↦
          block j = block k).card = 2)).card / 2 ≤ r ∧
      b₀ ∈ (Finset.univ : Finset α).image block ∧
      Matrix.trace ((matrixBlock
        (centeredTwoProjectionProduct
          (orthogonalConjugate Q (X * X.transpose))
          (orthogonalConjugate Q E) δ θ) block b₀) ^ (2 * p)) >
        (θ * η / 2) ^ (2 * p) := by
  classical
  letI : Finite (interiorCompressionIndex X E hE) :=
    Finite.of_injective (fun k : interiorCompressionIndex X E hE ↦ k.1)
      Subtype.val_injective
  letI : Fintype (interiorCompressionIndex X E hE) := Fintype.ofFinite _
  letI : DecidableEq (interiorCompressionIndex X E hE) := Classical.decEq _
  let Q := twoProjectionChangeOfBasis X E hX hE
  let block := twoProjectionBlock X E hX hE
  let yi₀ : pairedProjectionAdaptedIndex X E hE := Sum.inl (Sum.inl i)
  let yi := pairedProjectionAdaptedIndexEquiv X E hX hE yi₀
  let b₀ := block yi
  let lam := compressionEigenvalue X E hE i
  have hlam : 0 ≤ lam ∧ lam ≤ 1 := by
    simpa [lam] using compressionEigenvalue_mem_unitInterval X E hX hE i
  have hedge := bad_spectral_edge_large_root lam δ θ η hlam hδ.1 hθ hη hsmall
    (by simpa [lam] using hbad)
  dsimp only at hedge
  have hD : IsTwoProjectionBlockDecomposition (X * X.transpose) E Q block := by
    simpa [Q, block] using
      twoProjectionBlock_isTwoProjectionBlockDecomposition X E hX hE
  have hcount : ((Finset.univ : Finset α).filter (fun k ↦
      ((Finset.univ : Finset α).filter fun j ↦
        block j = block k).card = 2)).card / 2 ≤ r := by
    simpa [block] using
      twoProjectionBlock_two_block_index_card_div_two_le_rank X E hX hE
  have hb₀ : b₀ ∈ (Finset.univ : Finset α).image block := by
    exact Finset.mem_image.mpr ⟨yi, Finset.mem_univ yi, rfl⟩
  have hPii : orthogonalConjugate Q (X * X.transpose) yi yi = 1 := by
    dsimp only [Q, yi, yi₀]
    rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
    have hmul : (X * X.transpose) * rangeEigenbasis X E hE =
        rangeEigenbasis X E hE := by
      simp only [rangeEigenbasis, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X.transpose X, hX]
      simp
    have hyMul : Matrix.toEuclideanLin (X * X.transpose)
        (pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i))) =
          pairedProjectionAdaptedBasis X E hX hE (Sum.inl (Sum.inl i)) := by
      rw [pairedProjectionAdaptedBasis_inl_inl]
      ext a
      exact congrFun (congrFun hmul a) i
    rw [hyMul, pairedProjectionAdaptedBasis_inner]
    simp
  have hqpos : 0 < θ * η / 2 := div_pos (mul_pos hθ.1 hη.1) (by norm_num)
  have hqnonneg : 0 ≤ θ * η / 2 := hqpos.le
  refine ⟨Q, block, b₀, hD, hcount, hb₀, ?_⟩
  by_cases hint : 0 < lam ∧ lam < 1
  · let ii : interiorCompressionIndex X E hE := ⟨i, by simpa [lam] using hint⟩
    have hcard : ((Finset.univ : Finset α).filter fun j ↦
        block j = block yi).card = 2 := by
      change ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE yi₀))).card = 2
      rw [twoProjectionBlock_fiber_card_equiv X E hX hE yi₀]
      simpa [yi₀, lam, hint] using
        pairedProjectionAdaptedBlock_y_fiber_card X E hE i
    have hEii : orthogonalConjugate Q E yi yi = lam := by
      dsimp only [Q, yi, yi₀]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      have hentry := pairedProjectionAdapted_secondProjection_entry_y_interior
        X E hX hE (Sum.inl (Sum.inl i)) ii
      simpa [ii, lam] using hentry
    have htrace :=
      twoProjection_two_block_trace_eq_canonical_of_primary_diagonal
        (X * X.transpose) E Q block hD δ θ lam (2 * p) yi hcard hPii hEii
    obtain ⟨z₁, z₂, hsum, hprod, hlarge⟩ := hedge.2.2.2 hint.1 hint.2
    rw [htrace]
    exact twoProjectionPairTransferMatrix_trace_even_power_gt_of_large_real_root
      lam δ θ (θ * η / 2) z₁ z₂ p hp hlam hqnonneg
      hsum hprod hlarge
  · have hend : lam = 0 ∨ lam = 1 := by
      simpa [lam] using compressionEigenvalue_endpoint_of_not_interior
        X E hX hE i (by simpa [lam] using hint)
    have hcard : ((Finset.univ : Finset α).filter fun j ↦
        block j = block yi).card = 1 := by
      change ((Finset.univ : Finset α).filter (fun j ↦
        twoProjectionBlock X E hX hE j =
          twoProjectionBlock X E hX hE
            (pairedProjectionAdaptedIndexEquiv X E hX hE yi₀))).card = 1
      rw [twoProjectionBlock_fiber_card_equiv X E hX hE yi₀]
      simpa [yi₀, lam, hint] using
        pairedProjectionAdaptedBlock_y_fiber_card X E hE i
    have hEii : orthogonalConjugate Q E yi yi = lam := by
      dsimp only [Q, yi, yi₀]
      rw [orthogonalConjugate_twoProjectionChangeOfBasis_equiv_apply]
      have hentry := pairedProjectionAdapted_secondProjection_entry_y_endpoint
        X E hX hE (Sum.inl (Sum.inl i)) i (by simpa [lam] using hend)
      simpa [lam] using hentry
    have htrace := twoProjection_singleton_block_trace_pow_eq
      (X * X.transpose) E Q block hD δ θ 1 lam (2 * p) yi hcard hPii hEii
    rw [htrace]
    rcases hend with hzero | hone
    · apply even_power_strict_mono_of_abs_gt ((1 - δ) * (lam - θ))
        (θ * η / 2) p hp hqnonneg
      have hpositive : 0 < (1 - δ) * θ := by
        exact hqpos.trans (hedge.2.1 hzero)
      rw [hzero]
      convert hedge.2.1 hzero using 1 <;>
        rw [show (1 - δ) * (0 - θ) = -((1 - δ) * θ) by ring,
          abs_neg, abs_of_pos hpositive]
    · apply even_power_strict_mono_of_abs_gt ((1 - δ) * (lam - θ))
        (θ * η / 2) p hp hqnonneg
      have hpositive : 0 < (1 - δ) * (1 - θ) := by
        exact hqpos.trans (hedge.2.2.1 hone)
      rw [hone, abs_of_pos hpositive]
      exact hedge.2.2.1 hone

theorem two_projection_spectral_transfer_proof
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
  dsimp only
  have hδunit : 0 ≤ δ ∧ δ ≤ 1 :=
    ⟨hδ.1.le, hδ.2.trans (by norm_num)⟩
  have hθunit : 0 ≤ θ ∧ θ ≤ 1 :=
    ⟨hθ.1.le, hθ.2.le⟩
  obtain ⟨Q, block, hD, hcount⟩ :=
    twoProjectionBlockDecomposition_exists X E hX hE
  have hlower : Matrix.trace
      (((X * X.transpose - δ • 1) * (E - θ • 1)) ^ (2 * p)) ≥
      -2 * r * (δ * (1 - δ) * θ * (1 - θ)) ^ p := by
    simpa [centeredTwoProjectionProduct] using
      twoProjection_trace_even_power_lower_of_decomposition
        (X * X.transpose) E Q block hD hcount δ θ p hδunit hθunit
  refine ⟨hlower, ?_⟩
  intro η hη0 hη1 hsmall
  by_cases hnorm : euclideanOperatorNorm
      (θ⁻¹ • (X.transpose * E * X) - 1) > η
  · rw [if_pos hnorm]
    obtain ⟨i, hi⟩ := exists_compressionEigenvalue_deviation_of_operatorNorm_gt
      X E hE θ η hθ.1 hη0 hnorm
    obtain ⟨Qbad, blockBad, b₀, hDbad, hcountBad, hb₀, hbadBlock⟩ :=
      exists_twoProjection_bad_block_trace_gt X E hX hE δ θ η hp hδ hθ
        ⟨hη0, hη1⟩ hsmall i hi
    have hstrict := twoProjection_trace_plus_compensation_gt_of_bad_block
      (X * X.transpose) E Qbad blockBad hDbad hcountBad δ θ
        (θ * η / 2) p hδunit hθunit b₀ hb₀ hbadBlock
    exact le_of_lt (by simpa [centeredTwoProjectionProduct] using hstrict)
  · rw [if_neg hnorm]
    linarith


end Problem56.PaperV7
