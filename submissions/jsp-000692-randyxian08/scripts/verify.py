#!/usr/bin/env python3
"""Rebuild and audit BOTH questions; never reuse a prior successful verdict.

Run from any directory: python3 scripts/verify.py --prepare
--prepare downloads the pinned dependencies' mathlib cache. It does not update
package revisions. This script requires an installed Lean/Elan `lake` command.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

from source_audit import ROOT, audit

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_COMMIT = "5ed2965256430c3649e86755f9576b54eca72435"


class VerificationError(RuntimeError):
    pass


def parse_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    """Accept Lean's axiom reports only when every requested theorem appears."""
    found: dict[str, list[str]] = {}
    for name, raw in re.findall(
        r"'?([A-Za-z_][\w.]*)'?\s+depends on axioms:\s*\[([^\]]*)\]",
        output, flags=re.MULTILINE,
    ):
        values = [s.strip().strip("'") for s in raw.split(',') if s.strip()]
        found[name] = values
    for name in re.findall(
        r"'?([A-Za-z_][\w.]*)'?\s+does not depend on any axioms", output,
    ):
        found[name] = []
    missing = sorted(set(expected) - set(found))
    unexpected = {name: sorted(set(found[name]) - ALLOWED_AXIOMS)
                  for name in expected if name in found
                  and not set(found[name]) <= ALLOWED_AXIOMS}
    if missing or unexpected:
        raise VerificationError(json.dumps({
            "missing_axiom_reports": missing, "disallowed_axioms": unexpected,
        }, ensure_ascii=False))
    return {name: found[name] for name in expected}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true',
                        help='Fetch mathlib cache for the existing pinned manifest.')
    args = parser.parse_args()
    ev = ROOT / 'verification'
    ev.mkdir(exist_ok=True)
    now = dt.datetime.now(dt.timezone.utc)
    run_dir = ev / ('run-' + now.strftime('%Y%m%dT%H%M%SZ'))
    run_dir.mkdir(exist_ok=True)
    status: dict = {
        'checked_at_utc': now.isoformat(),
        'status': 'RUNNING',
        'scope': 'BOTH_QUESTIONS_FULL_QUANTIFIERS',
        'question_one_has_proof_body': True,
        'question_two_has_proof_body': True,
        'lean_compilation_performed': False,
        'lean_build_success': False,
        'standalone_compile_success': False,
        'kernel_axiom_audit_performed': False,
        'kernel_axiom_audit_success': False,
        'full_JSP_000692_lean_verified': False,
        'independent_statement_review_performed': False,
        'independent_mathematical_review_performed': False,
        'award_application_submitted': False,
        'award_eligibility_or_approval_verified': False,
        'commands': [],
        'logs_directory': str(run_dir.relative_to(ROOT)),
    }

    def save() -> None:
        text = json.dumps(status, ensure_ascii=False, indent=2) + '\n'
        (ev / 'status.json').write_text(text)
        (run_dir / 'status.json').write_text(text)

    def run(label: str, argv: list[str]) -> str:
        logfile = run_dir / (label + '.log')
        print('$ ' + ' '.join(argv), flush=True)
        completed = subprocess.run(
            argv, cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env={**os.environ, 'LEAN_ABORT_ON_PANIC': '1'},
            check=False,
        )
        logfile.write_text(completed.stdout)
        print(completed.stdout, end='' if completed.stdout.endswith('\n') else '\n')
        public_argv = [
            str(Path(arg).relative_to(ROOT)) if arg.startswith(str(ROOT) + os.sep)
            else Path(arg).name if os.path.isabs(arg) else arg
            for arg in argv
        ]
        status['commands'].append({
            'argv': public_argv, 'exit_code': completed.returncode,
            'log': str(logfile.relative_to(ROOT)),
        })
        save()
        if completed.returncode:
            raise VerificationError(f'{label} exited with {completed.returncode}')
        if re.search(r"declaration uses ['\"]?sorry|\bsorryAx\b", completed.stdout):
            raise VerificationError(f'{label} reported a placeholder proof')
        return completed.stdout

    save()
    try:
        source = audit()
        status['source_audit_status'] = source['status']
        status['source_sha256'] = source['sha256']
        status['theorems_requested_for_audit'] = source['theorems_requested_for_kernel_audit']
        config_names = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                        'DEPENDENCIES.lock.json', 'scripts/source_audit.py',
                        'scripts/verify.py']
        status['configuration_sha256'] = {
            name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in config_names
        }
        save()
        if source['status'] != 'PASS':
            raise VerificationError('source-only preflight failed')
        lake = shutil.which('lake')
        status['runtime_paths'] = {
            'lake': Path(lake).name if lake else None,
            'lean': Path(shutil.which('lean')).name if shutil.which('lean') else None,
        }
        if not lake:
            status['status'] = 'BLOCKED_NO_LEAN_RUNTIME'
            status['reason'] = 'No lake executable was found; no Lean compilation or axiom audit ran.'
            save()
            print(status['reason'])
            return 2
        version = run('lean-version', [lake, 'env', 'lean', '--version'])
        status['lean_version_output'] = version.strip()
        if not re.search(r'\bversion 4\.34\.0\b', version):
            raise VerificationError('The required compiler is Lean 4.34.0.')
        if args.prepare:
            run('mathlib-cache', [lake, 'exe', 'cache', 'get'])
        expected = json.loads((ROOT/'DEPENDENCIES.lock.json').read_text())['packages']
        if not shutil.which('git'):
            raise VerificationError('git is required to verify dependency commits.')
        revisions = {}
        for name, commit in expected.items():
            path = ROOT/'.lake/packages'/name
            if not path.is_dir():
                raise VerificationError(f'Missing dependency checkout: {name}. Use --prepare.')
            rev = run('revision-' + name,
                      ['git', '-C', str(path), 'rev-parse', 'HEAD']).strip()
            revisions[name] = rev
            if rev != commit:
                raise VerificationError(f'Dependency drift: {name}: {rev} != {commit}')
        status['dependency_revisions'] = revisions
        status['lean_compilation_performed'] = True
        run('lake-build', [lake, 'build', 'JSP692'])
        status['lean_build_success'] = True
        status['kernel_axiom_audit_performed'] = True
        output = run('axiom-audit', [lake, 'env', 'lean', 'Audit.lean'])
        axiom_map = parse_axioms(output, source['theorems_requested_for_kernel_audit'])
        (run_dir/'axioms.json').write_text(json.dumps(axiom_map, indent=2)+'\n')
        status['axiom_report'] = str((run_dir/'axioms.json').relative_to(ROOT))
        status['kernel_axiom_audit_success'] = True
        run('statement', [lake, 'env', 'lean', 'Statement.lean'])
        # Re-elaborate every project proof in a single Mathlib-only file, rather
        # than treating already-built local .olean files as the sole evidence.
        output = run('standalone', [lake, 'env', 'lean', 'JSP000692.lean'])
        parse_axioms(output, source['theorems_requested_for_kernel_audit'])
        status['standalone_compile_success'] = True
        status['full_JSP_000692_lean_verified'] = True
        status['status'] = 'PASS_LEAN_AND_AXIOM_AUDIT'
        status['reason'] = 'Both full-quantifier statements compiled and passed the requested axiom checks. No award decision is implied.'
        save()
        print(status['reason'])
        return 0
    except KeyboardInterrupt:
        status['status'] = 'INTERRUPTED'
        status['reason'] = 'Interrupted: no complete verification verdict is available.'
        save()
        return 130
    except (VerificationError, OSError, ValueError, subprocess.SubprocessError) as exc:
        status['status'] = 'FAIL'
        status['reason'] = str(exc)
        save()
        print('Verification did not succeed: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
