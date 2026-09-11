import Problem56.PaperV7.Certification
import Problem56.TargetBoundary

universe u_1
#check_public_type Problem56.PaperV7.certified_spectral_transfer : Problem56.PaperV7.Reference.SpectralTransferExpected.{u_1}
#check_public_type Problem56.PaperV7.certified_signed_trace : Problem56.PaperV7.Reference.SignedTraceExpected
#check_public_type Problem56.PaperV7.certified_bernoulli : Problem56.PaperV7.Reference.BernoulliExpected
#check_public_type Problem56.PaperV7.certified_small_rank : Problem56.PaperV7.Reference.SmallRankExpected
#check_public_type Problem56.PaperV7.certified_sampling : Problem56.PaperV7.Reference.GeneralSamplingExpected
#check_public_type Problem56.PaperV7.certified_explicit_main : Problem56.PaperV7.Reference.ExplicitPrescribedWidthExpected
#check_public_type Problem56.PaperV7.certified_main : Problem56.PaperV7.Reference.MainPrescribedWidthExpected
#reject_imports ComparatorChallenges.Problem56
