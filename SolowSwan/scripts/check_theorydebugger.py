"""Check general Solow algebra with CVC5 and reconstruct the evidence in Lean.

These finite polynomial checks do not certify the analytic production functions,
ODE existence, limits, or welfare claims; those have independent Lean proofs.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
OUTPUT = PROJECT / 'verification' / 'theorydebugger'


def mul(a, b): return ['*', a, b]
def sub(a, b): return ['-', a, b]
def add(a, b): return ['+', a, b]


def cases():
    return [
        ('rate_factorization', 'valid', {
            'variables': ['s', 'm', 'k', 'y', 'average'],
            'assumptions': [['=', 'y', mul('average', 'k')]],
            'goal': ['=', sub(mul('s', 'y'), mul('m', 'k')),
                     mul('k', sub(mul('s', 'average'), 'm'))],
            'witness': {'s': '1/2', 'm': 1, 'k': 1, 'y': 2, 'average': 2}}),
        ('strict_concavity_gives_negative_equilibrium_slope', 'valid', {
            'variables': ['s', 'm', 'k', 'y', 'mp'],
            'assumptions': [['>', 's', 0], ['>', 'k', 0],
                            ['=', mul('s', 'y'), mul('m', 'k')], ['<', mul('mp', 'k'), 'y']],
            'goal': ['<', mul('s', 'mp'), 'm'],
            'witness': {'s': '1/2', 'm': 1, 'k': 1, 'y': 2, 'mp': 1}}),
        ('saving_derivative_positive', 'valid', {
            'variables': ['D', 'y', 'response'],
            'assumptions': [['>', 'D', 0], ['>', 'y', 0], ['=', mul('D', 'response'), 'y']],
            'goal': ['>', 'response', 0], 'witness': {'D': 1, 'y': 2, 'response': 2}}),
        ('dilution_derivative_negative', 'valid', {
            'variables': ['D', 'k', 'response'],
            'assumptions': [['>', 'D', 0], ['>', 'k', 0],
                            ['=', mul('D', 'response'), mul(-1, 'k')]],
            'goal': ['<', 'response', 0], 'witness': {'D': 1, 'k': 2, 'response': -2}}),
        ('reversed_dilution_effect_is_false', 'refuted', {
            'variables': ['D', 'k', 'response'],
            'assumptions': [['>', 'D', 0], ['>', 'k', 0],
                            ['=', mul('D', 'response'), mul(-1, 'k')]],
            'goal': ['>', 'response', 0], 'witness': {'D': 1, 'k': 2, 'response': -2}}),
        ('weak_concavity_does_not_give_strict_slope', 'refuted', {
            'variables': ['s', 'm', 'k', 'y', 'mp'],
            'assumptions': [['>', 's', 0], ['>', 'k', 0],
                            ['=', mul('s', 'y'), mul('m', 'k')], ['<=', mul('mp', 'k'), 'y']],
            'goal': ['<', mul('s', 'mp'), 'm'],
            'witness': {'s': '1/2', 'm': 1, 'k': 1, 'y': 2, 'mp': 2}}),
        ('steady_consumption_resource_identity', 'valid', {
            'variables': ['s', 'm', 'k', 'y'],
            'assumptions': [['=', mul('s', 'y'), mul('m', 'k')]],
            'goal': ['=', mul(sub(1, 's'), 'y'), sub('y', mul('m', 'k'))],
            'witness': {'s': '1/2', 'm': 1, 'k': 1, 'y': 2}}),
        ('golden_saving_below_one', 'valid', {
            'variables': ['sg', 'm', 'k', 'y'],
            'assumptions': [['>', 'm', 0], ['>', 'k', 0], ['>', 'y', 0],
                            ['<', mul('m', 'k'), 'y'], ['=', mul('sg', 'y'), mul('m', 'k')]],
            'goal': ['<', 'sg', 1], 'witness': {'sg': '1/2', 'm': 1, 'k': 1, 'y': 2}}),
        ('zero_discount_has_no_strict_marginal_gap', 'refuted', {
            'variables': ['d', 'm', 'mp'],
            'assumptions': [['>=', 'd', 0], ['>', 'm', 0], ['=', 'mp', add('d', 'm')]],
            'goal': ['>', 'mp', 'm'], 'witness': {'d': 0, 'm': 1, 'mp': 1}}),
        ('effective_dilution_includes_technology', 'valid', {
            'variables': ['s', 'y', 'k', 'n', 'g', 'delta'], 'assumptions': [],
            'goal': ['=', sub(sub(mul('s', 'y'), mul('delta', 'k')), mul(add('n', 'g'), 'k')),
                     sub(mul('s', 'y'), mul(add(add('delta', 'n'), 'g'), 'k'))],
            'witness': {'s': '1/2', 'y': 2, 'k': 1, 'n': 1, 'g': 1, 'delta': 1}}),
    ]


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--theorydebugger', required=True, type=Path)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    td = args.theorydebugger.resolve()
    if not (td / 'src/theorydebugger/diagnose.py').is_file():
        parser.error('--theorydebugger must identify a TheoryDebugger source checkout')
    sys.path.insert(0, str(td / 'src'))
    from theorydebugger.backend import CVC5Backend
    from theorydebugger.certificates import LeanVerifier
    from theorydebugger.diagnose import diagnose
    from theorydebugger.ir import parse
    import cvc5
    inputs = OUTPUT / 'inputs'
    inputs.mkdir(parents=True, exist_ok=True)
    verifier = LeanVerifier(PROJECT, OUTPUT / 'certificates', args.lake)
    records = []
    for name, expected, data in cases():
        data['name'] = name
        (inputs / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8', newline='\n')
        result = diagnose(parse(data), CVC5Backend(), verifier)
        for certificate in result['certificates']:
            for field in ('source', 'compiler_log'):
                if field in certificate:
                    certificate[field] = Path(certificate[field]).relative_to(PROJECT).as_posix()
        records.append(result)
        (OUTPUT / 'results.json').write_text(json.dumps(records, indent=2, default=str) + '\n', encoding='utf-8', newline='\n')
        print(name, result['validity'], result['consistency'], flush=True)
        if result['validity'] != {'status': expected, 'evidence': 'lean_kernel'}:
            raise RuntimeError(json.dumps(result, indent=2, default=str))
        if result['consistency'] != {'status': 'consistent', 'evidence': 'lean_kernel'}:
            raise RuntimeError('Assumption feasibility was not checked')
        if result['warnings'] or any(c['status'] != 'lean_verified' for c in result['certificates']):
            raise RuntimeError('Incomplete or rejected certificate')
    environment = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Ten finite polynomial diagnostics; the analytic results are proved independently in Lean.',
        'lean': subprocess.check_output([args.lake, 'env', 'lean', '--version'], cwd=PROJECT, text=True).strip(),
        'cvc5': cvc5.Solver().getVersion().decode(),
        'mathlib_manifest_sha256': digest(PROJECT / 'lake-manifest.json'),
        'script_sha256': digest(Path(__file__)),
        'theorydebugger_source_sha256': {p.relative_to(td).as_posix(): digest(p) for p in sorted((td / 'src/theorydebugger').glob('*.py'))},
        'cases': len(records), 'certificates': sum(len(r['certificates']) for r in records),
        'input_sha256': {p.name: digest(p) for p in sorted(inputs.glob('*.json'))},
    }
    (OUTPUT / 'environment.json').write_text(json.dumps(environment, indent=2) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
