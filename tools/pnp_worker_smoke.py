#!/usr/bin/env python3
"""Check the real verifier on a synthetic True theorem before credentials or leases."""

import argparse
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

from pnp_worker import Worker, WorkerError, digest, require_checker_acceptance


MODULE = "PEqualNP.Outside.WorkerSmoke"
SOURCE = b"import Mathlib\n\ntheorem PEqualNP.Outside.WorkerSmoke : True := by trivial\n"
OUTPUT_SUFFIXES = {
    "lib/lean": (".olean", ".olean.hash", ".olean.private", ".olean.private.hash",
                 ".olean.server", ".olean.server.hash", ".ilean", ".ilean.hash", ".trace",
                 ".ir", ".ir.hash"),
    "ir": (".c", ".c.hash", ".setup.json", ".c.o", ".c.o.hash", ".c.o.trace",
           ".c.o.export", ".c.o.export.hash", ".c.o.export.trace"),
}


class NoNetwork:
    def request(self, *_args, **_kwargs):
        raise WorkerError("The technical smoke check must never use a network client")


def output_paths(upstream):
    return [upstream / "lean/.lake/build" / directory / "PEqualNP/Outside" / ("WorkerSmoke" + suffix)
            for directory, suffixes in OUTPUT_SUFFIXES.items() for suffix in suffixes]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-dir", type=Path, required=True)
    parser.add_argument("--elan-home", type=Path, required=True)
    parser.add_argument("--compiler-user", default="pnp_build")
    args = parser.parse_args()
    if os.environ.get("GITHUB_TOKEN"):
        print("Smoke check refused: it must run before the credential-bearing step", file=sys.stderr)
        return 1
    os.umask(0o077)
    worker = None
    created = False
    proof = args.upstream_dir.resolve() / "lean/PEqualNP/Outside/WorkerSmoke.lean"
    outputs = output_paths(args.upstream_dir.resolve())
    result = 1
    try:
        if any(path.exists() or path.is_symlink() for path in [proof, *outputs]):
            raise WorkerError("Synthetic smoke source or outputs already exist; nothing was overwritten")
        worker = Worker(args, github=NoNetwork(), desk=NoNetwork())
        def stop(_signum, _frame):
            worker.stopping = True
        signal.signal(signal.SIGTERM, stop)
        signal.signal(signal.SIGINT, stop)
        with proof.open("xb") as stream:
            created = True
            stream.write(SOURCE)
        proof.chmod(0o644)
        with tempfile.TemporaryDirectory(prefix="smoke-", dir=worker.private) as directory:
            private = Path(directory)
            statement = private / "statement.txt"
            imports = private / "outside-imports.txt"
            statement.write_text("True", encoding="utf-8")
            imports.write_text("", encoding="utf-8")
            code, output = worker.run_checker(proof, statement, imports)
            print(f"Technical checker process exit={code}", flush=True)
            require_checker_acceptance(code, output, MODULE, SOURCE)
            if proof.read_bytes() != SOURCE:
                raise WorkerError("Synthetic source changed during the official checker")
            print("Technical smoke accepted by the real checker; source sha256=" + digest(SOURCE), flush=True)
            result = 0
    except WorkerError as exc:
        print("Technical smoke failed: " + str(exc), file=sys.stderr)
    except Exception as exc:
        print("Technical smoke failed: " + type(exc).__name__, file=sys.stderr)
    finally:
        if worker is not None:
            worker.stop_processes()
        if created:
            # Only this synthetic module's exact known outputs may be removed.
            # No recursive deletion and no directory or wildcard is passed to rm.
            try:
                proof.unlink(missing_ok=True)
                cleanup = subprocess.run(["sudo", "-n", "rm", "-f", "--", *map(str, outputs)],
                                         capture_output=True, timeout=15)
                if cleanup.returncode or any(path.exists() or path.is_symlink() for path in [proof, *outputs]):
                    raise WorkerError("Synthetic module cleanup was incomplete")
            except Exception:
                print("Technical smoke failed: synthetic module cleanup was incomplete", file=sys.stderr)
                result = 1
    return result


if __name__ == "__main__":
    sys.exit(main())
