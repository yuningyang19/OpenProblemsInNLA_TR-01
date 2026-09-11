#!/usr/bin/env python3
"""Recheck source identity, public types, axioms and optional fresh proof evidence."""
import argparse, hashlib, json, pathlib, re, subprocess, sys, time
ROOT = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'audit'))
from graph_checks import parse_log, validate_records

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def check_sources():
    manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
    for name, expected in manifest['files'].items():
        path = ROOT / name
        require(path.is_file(), 'Missing certified input: ' + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                'Changed certified input: ' + name)
    return manifest

def run(name, command):
    print('Running:', ' '.join(command), flush=True)
    started = time.monotonic()
    path = ROOT / 'build' / (name + '.log')
    with path.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    require(result.returncode == 0, 'FAILED; inspect ' + str(path))
    return {'command': command, 'returncode': result.returncode,
            'elapsed_seconds': time.monotonic() - started,
            'log': str(path.relative_to(ROOT)),
            'log_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh-kernel', action='store_true', help='replay imported proof objects with leanchecker --fresh')
    parser.add_argument('--graph', action='store_true', help='regenerate and validate all 407 transitive target graphs')
    parser.add_argument('--semantic', action='store_true', help='run the seven isolated positive/negative Lean clients')
    args = parser.parse_args()
    manifest = check_sources()
    (ROOT / 'build').mkdir(exist_ok=True)
    results = {}
    results['build'] = run('build', ['lake', 'build', 'Problem56.PaperV7.Certification', 'Problem56.PaperV7.BoundaryChecks'])
    # Force the type-check client to execute even if Lake reused its object.
    results['boundary'] = run('boundary', ['lake', 'env', 'lean', 'Problem56/PaperV7/BoundaryChecks.lean'])
    results['axioms'] = run('axioms', ['lake', 'env', 'lean', 'Problem56/PaperV7/AxiomAudit.lean'])
    axiom_text = (ROOT / results['axioms']['log']).read_text()
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_text)
    for target, axioms in records:
        require(set(a.strip() for a in axioms.split(',') if a.strip()) <=
                {'propext', 'Classical.choice', 'Quot.sound'}, 'Forbidden axiom: ' + target)
    required = {'Problem56.PaperV7.certified_' + s for s in
                ['main', 'explicit_main', 'spectral_transfer', 'signed_trace', 'bernoulli', 'small_rank', 'sampling']}
    require(required <= {n for n, _ in records}, 'Missing public axiom report')
    graph_path = ROOT / 'audit' / 'combined_audit_final.log.gz'
    if args.graph:
        results['graph'] = run('graph', ['lake', 'env', 'lean', 'Problem56/PaperV7/CombinedAudit.lean'])
        graph_path = ROOT / results['graph']['log']
    targets, nodes = parse_log(graph_path)
    graph = validate_records(targets, nodes, json.loads((ROOT / 'audit/target_inventory.json').read_text()))
    correspondence = json.loads((ROOT / 'audit/final_candidate_correspondence.json').read_text())
    for row in correspondence['source_rows'] + correspondence['additional_interfaces']:
        mapped = list(row.get('current_theorem_ids', [])) + list(row.get('current_definition_ids', []))
        require(all(n in nodes for n in mapped), 'Missing mapped declaration: ' + row['id'])
    if args.semantic:
        results['semantic'] = run('semantic', [sys.executable, 'audit/semantic_regressions.py'])
    if args.fresh_kernel:
        results['fresh_kernel'] = run('fresh_kernel', ['lake', 'env', 'leanchecker', '--fresh', '-v', 'Problem56.PaperV7.Certification'])
    require(check_sources() == manifest, 'Sources changed during verification')
    result = {'status': 'PASS', 'checked_inputs': len(manifest['files']),
              'axiom_reports': len(records), 'graph_targets': graph['target_count'],
              'graph_evidence': 'fresh' if args.graph else 'archived with certified source binding',
              'fresh_kernel_run': args.fresh_kernel, 'semantic_cases_run': args.semantic,
              'source_commit': manifest['mathematical_source_commit'], 'commands': results}
    (ROOT / 'build/verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS. Evidence: build/verification.json')

if __name__ == '__main__':
    main()
