import Problem56.PaperV6.Certification
import Problem56.PaperV7.Main
import Problem56.PaperV7.GeneralSamplingJoint
import Problem56.PaperV7.Expected
import Problem56.PaperV7.EntryBridges
import Problem56.PaperV7.SamplingInterfaceBridges

namespace Problem56.PaperV7

theorem certified_spectral_transfer : Reference.SpectralTransferExpected :=
  @two_projection_spectral_transfer

theorem certified_signed_trace : Reference.SignedTraceExpected :=
  @signed_trace_proposition

theorem certified_bernoulli : Reference.BernoulliExpected :=
  @bernoulli_coordinate_sampling_corollary

theorem certified_small_rank : Reference.SmallRankExpected :=
  @small_rank_second_moment

theorem certified_sampling : Reference.GeneralSamplingExpected := by
  intro Ω α _ _ _ μ _ r k X hX horth ε γ hε0 hε1 _hγ hk0 hkn hminus hplus
  exact general_sampling Ω α μ r k X hX horth ε γ hε0 hε1 hk0 hkn hminus hplus

theorem certified_explicit_main : Reference.ExplicitPrescribedWidthExpected := by
  obtain ⟨C, hCeq, hC, hmain⟩ := main_prescribed_width_ose
  rw [hCeq] at hC hmain
  refine ⟨hC, ?_⟩
  intro m r ε hr hrn hε0 hε1
  exact (hmain m r ε hr hrn hε0 hε1).2.2

theorem certified_main : Reference.MainPrescribedWidthExpected := by
  refine ⟨(explicitUniversalConstant : ℝ), ?_, certified_explicit_main.2⟩
  exact_mod_cast certified_explicit_main.1

end Problem56.PaperV7
