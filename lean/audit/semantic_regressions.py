#!/usr/bin/env python3
"""Run isolated actual Lean type mutations, alongside positive endpoint clients."""
import json,pathlib,subprocess,tempfile
L=pathlib.Path(__file__).resolve().parents[1];E=L/'build';E.mkdir(exist_ok=True)
base='import Problem56.PaperV7.Certification\nimport Problem56.TargetBoundary\n'
cases=[('old_selected_width_rejected',base+'#check_public_type Problem56.main_universal_ose : Problem56.PaperV7.Reference.MainPrescribedWidthExpected\n',False),
('old_half_density_transfer_rejected',base+'example : Problem56.PaperV7.Reference.SpectralTransferExpected := @Problem56.two_projection_spectral_transfer\n',False),
('old_half_density_trace_rejected',base+'example : Problem56.PaperV7.Reference.SignedTraceExpected := @Problem56.signed_trace_proposition\n',False),
('old_selected_small_rank_tail_rejected',base+'example : Problem56.PaperV7.Reference.SmallRankExpected := @Problem56.small_rank_second_moment\n',False),
('wrong_main_constant_rejected',base+'#check_public_type Problem56.PaperV7.certified_main : False\n',False),
('current_exact_boundary',base+'#check_public_type Problem56.PaperV7.certified_main : Problem56.PaperV7.Reference.MainPrescribedWidthExpected\n#check_public_type Problem56.PaperV7.certified_sampling : Problem56.PaperV7.Reference.GeneralSamplingExpected\n',True),
('full_sample_endpoint_and_epsilon_extension',base+'''open Problem56 Problem56.PaperV7
example (V : Matrix (WalshIndex 0) (Fin 1) ℝ) (hV : OrthonormalFrame V) :
    frameFailureProbability (k := walshCard 0) (3/4) V = 0 :=
  frameFailureProbability_full_sample V hV _ (by norm_num)
example {m r k : ℕ} (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (hV : OrthonormalFrame V) (hk : 1 ≤ k ∧ k ≤ walshCard m) :
    frameFailureProbability (k := k) 2 V ≤ (r : ℝ) * (r+1) / ((k : ℝ)*2^2) :=
  small_rank_failure_bound V hV hk 2 (by norm_num)
''',True)]
results=[]
with tempfile.TemporaryDirectory(prefix='v7-semantic-') as d:
 for name,src,success in cases:
  p=pathlib.Path(d)/'Case.lean';p.write_text(src)
  x=subprocess.run(['lake','env','lean',str(p)],cwd=L,capture_output=True,text=True)
  out=x.stdout+x.stderr
  ok=(x.returncode==0) if success else (x.returncode!=0 and ('type differs' in out or 'Type mismatch' in out or 'type mismatch' in out))
  results.append({'name':name,'source':src,'command':['lake','env','lean',str(p)],'returncode':x.returncode,'expected':'success' if success else 'type rejection','output':out,'pass':ok})
(E/'semantic_regressions.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps([{k:r[k] for k in ['name','returncode','pass']} for r in results],indent=2));raise SystemExit(0 if all(r['pass'] for r in results) else 1)
