#!/usr/bin/env python3
"""Validate one fixed, already leased reduction; never allocate or publish work."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

sys.path.insert(0, '/opt/pnp-controller')
from pnp_worker import Worker, WorkerError


MODULE = 'PEqualNP.Outside.R_meta_2462_724'
RELATIVE = 'lean/PEqualNP/Outside/R_meta_2462_724.lean'
PROOF_SHA = 'c6030474bbdba9fa7913602051a354cd0262ca9d0cc89597377cc216d2eb7361'
STATEMENT_SHA = '07cab47dcc3e5899ea05db162e1c7b27b292b1b8fbbe8c00fac4bf1e4cfc1dff'


class NoNetwork:
    def request(self, *args, **kwargs):
        raise WorkerError('Validation has no network client and never owns a lease')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, required=True)
    parser.add_argument('--upstream-dir', type=Path, required=True)
    parser.add_argument('--elan-home', type=Path, required=True)
    parser.add_argument('--compiler-user', default='pnp_build')
    args = parser.parse_args()
    if os.environ.get('GITHUB_TOKEN') or os.environ.get('GH_TOKEN'):
        raise WorkerError('Validation must receive no API token')
    os.umask(0o077)
    source = (args.source_dir / 'R_meta_2462_724.lean').read_bytes()
    statement = (args.source_dir / 'statement.txt').read_bytes()
    if digest(source) != PROOF_SHA or digest(statement) != STATEMENT_SHA:
        raise WorkerError('Fixed candidate or assigned statement hash mismatch')
    upstream = args.upstream_dir.resolve()
    target = upstream / RELATIVE
    if target.exists() or target.is_symlink():
        raise WorkerError('Candidate path already exists upstream; nothing was overwritten')
    worker = Worker(args, github=NoNetwork(), desk=NoNetwork())
    worker.check_wrapper = Path('/opt/pnp-controller/check-reduction.sh')
    def stop(_signum, _frame):
        worker.stopping = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    output = ''
    try:
        with target.open('xb') as stream:
            stream.write(source)
        target.chmod(0o644)
        with tempfile.TemporaryDirectory(prefix='reduction-', dir=worker.private) as tmp:
            private = Path(tmp)
            statement_path = private / 'statement.txt'
            imports_path = private / 'imports.json'
            statement_path.write_bytes(statement)
            imports_path.write_text(json.dumps(['PEqualNP.Defs']), encoding='utf-8')
            guard = upstream / '.github/scripts/outside-guard.mjs'
            for command in [
                ['node', str(guard), 'imports', str(target), str(imports_path), RELATIVE, 'reduce'],
                ['node', str(guard), 'closure', str(upstream), str(imports_path), RELATIVE, str(private), 'reduce'],
            ]:
                checked = subprocess.run(command, cwd=upstream, text=True, capture_output=True, timeout=30)
                if checked.returncode:
                    print(checked.stdout[-8000:] + checked.stderr[-8000:])
                    raise WorkerError('A required source or import guard failed')
            code, output = worker.run_checker(target, statement_path, private / 'outside-imports.txt')
            print('VALIDATION_CHECKER_EXIT ' + str(code), flush=True)
            lines = output.strip().splitlines()
            manifests = [json.loads(line[9:]) for line in lines if line.startswith('MANIFEST ')]
            children = [line for line in lines if line.startswith('CHILD ')]
            accepted = (
                code == 0 and lines and lines[-1].startswith('ACCEPTED (reduce)')
                and len(manifests) == 1 and len(children) == 2
                and 'CHILDREN 2' in lines
                and not any(line.startswith('REJECTED') or line.startswith('CHECKER FAULT') for line in lines)
            )
            if not accepted:
                raise WorkerError('The complete checker did not accept this reduction')
            manifest = manifests[0]
            if not any(item.get('module') == MODULE and item.get('sha256') == PROOF_SHA
                       for item in manifest.get('rests_on', [])):
                raise WorkerError('Checker manifest does not identify the fixed candidate bytes')
            if target.read_bytes() != source:
                raise WorkerError('Candidate changed during validation')
            for line in children:
                print(line, flush=True)
            print(lines[-1], flush=True)
            report = {
                'gap_id': 'L-meta-2462', 'kind': 'reduce', 'module': MODULE,
                'status': 'accepted_by_complete_project_checker',
                'proof_sha256': PROOF_SHA, 'statement_sha256': STATEMENT_SHA,
                'upstream_sha': os.environ['PNP_UPSTREAM_SHA'],
                'checker_exit': code, 'children': 2,
                'lease_owned_by_this_job': False,
                'upstream_pr_created': False,
            }
            print('VALIDATION_REPORT ' + json.dumps(report, sort_keys=True), flush=True)
            summary = os.environ.get('GITHUB_STEP_SUMMARY')
            if summary:
                with open(summary, 'a', encoding='utf-8') as stream:
                    stream.write('## Reduction validation\n\nThe complete project checker accepted the fixed reduction.\n\n')
                    stream.write('No task was allocated and no upstream pull request was opened by this validation job.\n\n')
                    stream.write('```json\n' + json.dumps(report, indent=2) + '\n```\n')
            return 0
    except Exception:
        for line in output[-12000:].splitlines():
            print('VALIDATION_LOG ' + line, flush=True)
        raise
    finally:
        worker.stop_processes()


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        print('VALIDATION_FAILED ' + str(exc), file=sys.stderr)
        sys.exit(1)
