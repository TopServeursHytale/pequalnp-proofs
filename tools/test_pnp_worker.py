#!/usr/bin/env python3
"""Focused offline tests and a real, credential-free build-isolation probe.

The isolation mode belongs before the credential-bearing coordinator step in CI.
It uses a fake lake executable and temporary markers, never a real task or lease.
"""

import argparse
import base64
import copy
import datetime as dt
import importlib.util
import json
import os
from pathlib import Path
import pwd
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


MODULE = None


def worker_module():
    global MODULE
    if MODULE is None:
        path = Path(__file__).with_name("pnp_worker.py")
        spec = importlib.util.spec_from_file_location("pnp_worker_under_test", path)
        MODULE = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = MODULE
        spec.loader.exec_module(MODULE)
    return MODULE


def synthetic_assignment():
    return {
        "gap": {
            "id": "L-meta-999999",
            "title": "Offline fixture",
            "file": "lean/PEqualNP/Outside/L_meta_999999.lean",
            "module": "PEqualNP.Outside.L_meta_999999",
            "statement": "True",
            "imports": [],
            "kind": "check",
            "weight": 1,
        },
        "lease": {
            "id": "OFFLINE_LEASE_MARKER_NOT_A_CREDENTIAL",
            "expires_at": "2099-01-01T00:20:00Z",
        },
    }


class AssignmentTests(unittest.TestCase):
    def test_exact_statement_survives_validation(self):
        w = worker_module()
        assignment = synthetic_assignment()
        assignment["gap"]["statement"] = "∀ n : Nat,\n  n = n"
        gap, lease = w.validate_assignment(assignment)
        self.assertEqual(gap["statement"], assignment["gap"]["statement"])
        self.assertEqual(lease, assignment["lease"]["id"])

    def test_missing_lease_is_not_a_work_assignment(self):
        w = worker_module()
        assignment = synthetic_assignment()
        assignment["lease"] = None
        with self.assertRaises(w.WorkerError):
            w.validate_assignment(assignment)

    def test_path_escape_is_rejected(self):
        w = worker_module()
        assignment = synthetic_assignment()
        assignment["gap"]["file"] = "lean/PEqualNP/Outside/../../CheckLemma.lean"
        with self.assertRaises(w.WorkerError):
            w.validate_assignment(assignment)

    def test_shell_syntax_is_not_an_import_name(self):
        w = worker_module()
        assignment = synthetic_assignment()
        assignment["gap"]["imports"] = ["PEqualNP.Defs; touch /tmp/never-run"]
        with self.assertRaises(w.WorkerError):
            w.validate_assignment(assignment)


class SubmissionRequestTests(unittest.TestCase):
    SHA = "a" * 40
    NOW = dt.datetime(2099, 1, 1, 12, 0, tzinfo=dt.timezone.utc)

    def request(self, **changes):
        request = {
            "nonce": "b" * 32,
            "proof_commit_sha": self.SHA,
            "requested_at": (self.NOW - dt.timedelta(seconds=20)).isoformat(),
        }
        request.update(changes)
        return request

    def test_recent_request_for_exact_commit_is_valid(self):
        request = self.request()
        result = worker_module().validate_submission_request(request, self.SHA, self.NOW)
        self.assertIsNotNone(result)
        self.assertEqual(result["nonce"], request["nonce"])

    def test_wrong_commit_is_rejected(self):
        result = worker_module().validate_submission_request(
            self.request(proof_commit_sha="c" * 40), self.SHA, self.NOW
        )
        self.assertIsNone(result)

    def test_old_and_future_requests_are_rejected(self):
        for delta in [dt.timedelta(days=-1), dt.timedelta(days=1)]:
            with self.subTest(delta=delta):
                result = worker_module().validate_submission_request(
                    self.request(requested_at=(self.NOW + delta).isoformat()),
                    self.SHA,
                    self.NOW,
                )
                self.assertIsNone(result)

    def test_nonce_is_required(self):
        result = worker_module().validate_submission_request(
            self.request(nonce=""), self.SHA, self.NOW
        )
        self.assertIsNone(result)


class PublicStateTests(unittest.TestCase):
    def test_worker_update_preserves_pending_controller_command(self):
        command = {
            "nonce": "d" * 32,
            "proof_commit_sha": "e" * 40,
            "requested_at": "2099-01-01T00:00:00Z",
        }
        current = {"phase": "proof_ready", "request_submission": command}
        merged = worker_module().merge_public_state(
            current, {"last_lease_beat_utc": "2099-01-01T00:00:01Z"}
        )
        self.assertEqual(merged["request_submission"], command)

    def test_private_top_level_data_is_not_republished(self):
        w = worker_module()
        marker = "OFFLINE_PRIVATE_MARKER_NOT_A_CREDENTIAL"
        for current, patch in [
            ({"phase": "searching", "lease": {"id": marker}}, {"phase": "finished"}),
            ({"phase": "searching"}, {"phase": "finished", "token": marker}),
        ]:
            with self.subTest(current=current, patch=patch):
                try:
                    merged = w.merge_public_state(current, patch)
                except w.WorkerError:
                    continue
                self.assertNotIn(marker, json.dumps(merged))

    def test_private_nested_fields_are_not_republished(self):
        marker = "OFFLINE_PRIVATE_MARKER_NOT_A_CREDENTIAL"
        current = {
            "gap": {"id": "L-meta-999999", "lease": marker},
            "request_submission": {"nonce": "d" * 32, "token": marker},
            "submission_permit": {"expires_at": "2099-01-01T00:00:00Z", "lease": marker},
            "release": {"confirmed": False, "url": marker},
        }
        merged = worker_module().merge_public_state(current, {"phase": "blocked"})
        self.assertNotIn(marker, json.dumps(merged))


class StateStoreTests(unittest.TestCase):
    NOW = SubmissionRequestTests.NOW

    def record(self, state, sha):
        return {"content": base64.b64encode(json.dumps(state).encode()).decode(), "sha": sha}

    def test_cas_conflict_rereads_and_preserves_new_controller_command(self):
        w = worker_module()
        new_command = {"nonce": "e" * 32, "proof_commit_sha": "a" * 40,
                       "requested_at": w.iso(self.NOW)}
        github = mock.Mock()
        github.request.side_effect = [
            self.record({"phase": "proof_ready"}, "first-state"),
            w.APIError(409),
            self.record({"phase": "proof_ready", "request_submission": new_command}, "new-state"),
            {},
        ]
        sleep = mock.Mock()
        store = w.StateStore(github, "offline/fixture", "b" * 40, lambda: self.NOW, sleep, lambda: ())
        result = store.update({"last_lease_beat_utc": w.iso(self.NOW)})
        writes = [call for call in github.request.call_args_list if call.args[0] == "PUT"]
        self.assertEqual(len(writes), 2)
        payload = writes[-1].args[2]
        published = json.loads(base64.b64decode(payload["content"]))
        self.assertEqual(payload["sha"], "new-state")
        self.assertEqual(published["request_submission"], new_command)
        self.assertEqual(result["request_submission"], new_command)
        sleep.assert_called_once_with(1)

    def test_actual_private_markers_are_blocked_before_any_write(self):
        w = worker_module()
        lease = "OFFLINE_LEASE_MARKER_NOT_A_CREDENTIAL"
        token = "OFFLINE_TOKEN_MARKER_NOT_A_CREDENTIAL"
        for marker in (lease, token):
            with self.subTest(marker=marker):
                github = mock.Mock()
                github.request.return_value = self.record({}, "state")
                store = w.StateStore(github, "offline/fixture", "b" * 40,
                                     lambda: self.NOW, mock.Mock(), lambda: (lease, token))
                with self.assertRaises(w.WorkerError) as caught:
                    store.update({"reason": marker})
                self.assertNotIn(marker, str(caught.exception))
                self.assertEqual([call.args[0] for call in github.request.call_args_list], ["GET"])


def synthetic_pr():
    w = worker_module()
    return {
        "state": "open", "merged": False, "user": {"login": "offline"},
        "head": {"repo": {"full_name": "offline/fixture"},
                 "ref": "pnp-proof-l-meta-999999-123", "sha": "a" * 40},
        "base": {"repo": {"full_name": w.UPSTREAM}, "ref": "main"},
        "changed_files": 1,
    }, [{"filename": synthetic_assignment()["gap"]["file"], "status": "added"}]


class PullRequestTests(unittest.TestCase):
    def verified(self, pr, files):
        return worker_module().verified_pr(
            pr, files, "offline/fixture", "pnp-proof-l-meta-999999-123", "a" * 40,
            synthetic_assignment()["gap"]["file"], "offline",
        )

    def test_exact_head_base_author_and_added_file_are_required(self):
        pr, files = synthetic_pr()
        self.assertTrue(self.verified(pr, files))
        changes = [
            ("head", "sha", "b" * 40), ("head", "ref", "other-branch"),
            ("base", "ref", "other-base"), ("user", "login", "other-author"),
            ("head", "repo", {"full_name": "other/fixture"}),
            ("base", "repo", {"full_name": "other/upstream"}),
        ]
        for section, field, value in changes:
            with self.subTest(section=section, field=field):
                changed = copy.deepcopy(pr)
                changed[section][field] = value
                self.assertFalse(self.verified(changed, files))
        for changed_files in [
            files + [{"filename": "README.md", "status": "modified"}],
            [{"filename": files[0]["filename"], "status": "modified"}],
            [{"filename": "lean/CheckLemma.lean", "status": "added"}],
        ]:
            with self.subTest(files=changed_files):
                self.assertFalse(self.verified(pr, changed_files))


class CheckerAcceptanceTests(unittest.TestCase):
    def test_a_killed_checker_or_mismatched_manifest_never_counts_as_acceptance(self):
        w = worker_module()
        source = b"theorem OfflineFixture : True := by trivial\n"
        module = "PEqualNP.Outside.WorkerSmoke"
        manifest = {"rests_on": [{"module": module, "sha256": w.digest(source)}]}
        accepted = "MANIFEST " + json.dumps(manifest) + "\nACCEPTED (check)\n"
        self.assertEqual(w.require_checker_acceptance(0, accepted, module, source), manifest)
        for code, output, expected_source in [
            (137, accepted, source), (124, accepted, source),
            (0, "REJECTED synthetic fixture\n" + accepted, source),
            (0, accepted, source + b"-- changed\n"),
            (0, "ACCEPTED (check)\n", source),
        ]:
            with self.subTest(code=code, output=output):
                with self.assertRaises(w.WorkerError):
                    w.require_checker_acceptance(code, output, module, expected_source)


class WorkerBehaviorTests(unittest.TestCase):
    NOW = SubmissionRequestTests.NOW

    def setUp(self):
        self.w = worker_module()
        self.temporary = tempfile.TemporaryDirectory(prefix="pnp-offline-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.environment = mock.patch.dict(os.environ, {
            "GITHUB_REPOSITORY": "offline/fixture", "GITHUB_RUN_ID": "123",
            "GITHUB_TOKEN": "OFFLINE_TOKEN_MARKER_NOT_A_CREDENTIAL",
            "PNP_PRIVATE_DIR": str(self.root / "private"),
            "PNP_TC_BIN": str(self.root / "toolchain"),
            "PNP_GITCONFIG": str(self.root / "gitconfig"),
        }, clear=True)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.github, self.desk = mock.Mock(), mock.Mock()
        self.args = SimpleNamespace(upstream_dir=self.root / "upstream",
                                    elan_home=self.root / "elan", compiler_user="pnp_build",
                                    max_wait_minutes=90)
        self.worker = self.w.Worker(self.args, github=self.github, desk=self.desk,
                                   now=lambda: self.NOW, sleep=mock.Mock())
        self.worker.stop_processes = mock.Mock()
        self.worker.store = mock.Mock()
        self.worker.store.update.side_effect = lambda patch: self.w.merge_public_state(self.worker.state, patch)
        self.worker.upstream_sha = "b" * 40

    def ready_proof(self):
        assignment = synthetic_assignment()
        worker = self.worker
        worker.gap = assignment["gap"]
        worker.lease_id = assignment["lease"]["id"]
        worker.lease_alive = True
        worker.last_beat = self.NOW
        worker.proof = b"import Mathlib\ntheorem PEqualNP.Outside.L_meta_999999 : True := by trivial\n"
        worker.proof_sha256 = self.w.digest(worker.proof)
        worker.proof_branch = "pnp-proof-l-meta-999999-123"
        worker.proof_commit_sha = "a" * 40
        worker.state = {
            "phase": "proof_ready", "local_checker": "accepted",
            "submission_window_expires_at": self.w.iso(self.NOW + dt.timedelta(minutes=30)),
            "submission_permit": None,
        }
        path = worker.upstream / worker.gap["file"]
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(worker.proof)
        return worker

    def request(self, **changes):
        request = {"nonce": "c" * 32, "proof_commit_sha": "a" * 40,
                   "requested_at": self.w.iso(self.NOW)}
        request.update(changes)
        return {"request_submission": request}

    def registry(self):
        return 200, json.dumps({"gaps": [self.worker.gap]}).encode()

    def test_empty_assignment_holds_no_lease_and_sends_no_post(self):
        self.desk.request.side_effect = [
            (200, b"Offline participation instructions"),
            (200, b'{"gaps": []}'),
            (200, b'{"gap": null, "retry_after_s": 450}'),
        ]
        self.assertFalse(self.worker.acquire())
        self.assertFalse(self.worker.lease_alive)
        self.assertIsNone(self.worker.lease_id)
        self.assertEqual(self.worker.state["phase"], "waiting")
        self.assertEqual(self.worker.state["retry_after_s"], 450)
        self.assertEqual(self.worker.state["next_attempt_not_before_utc"],
                         self.w.iso(self.NOW + dt.timedelta(seconds=450)))
        self.assertTrue(all(len(call.args) == 1 or call.args[1] == "GET"
                            for call in self.desk.request.call_args_list))
        self.github.request.assert_not_called()

    def test_410_stops_processes_and_prevents_submission_permit(self):
        worker = self.ready_proof()
        self.desk.request.return_value = (410, b'{"error":"gone"}')
        with self.assertRaises(self.w.LeaseLost):
            worker.beat()
        self.assertFalse(worker.lease_alive)
        worker.stop_processes.assert_called_once()
        self.assertFalse(worker.process_submission_request(self.request()))
        self.assertIsNone(worker.state["submission_permit"])
        self.assertEqual(self.desk.request.call_count, 1)
        self.github.request.assert_not_called()

    def test_release_transport_failure_never_claims_confirmation(self):
        worker = self.ready_proof()
        self.desk.request.side_effect = self.w.WorkerError("Offline simulated timeout")
        result = worker.release("out_of_time")
        self.assertEqual(result, {"attempted": True, "confirmed": False,
                                  "reason": "out_of_time", "transport_failed": True})
        self.assertTrue(worker.lease_alive)
        self.assertEqual(worker.release("out_of_time"), result)
        self.assertEqual(self.desk.request.call_count, 1)

    def test_wrong_pr_head_does_not_release_as_submitted(self):
        worker = self.ready_proof()
        pr, files = synthetic_pr()
        pr["head"]["sha"] = "e" * 40
        self.github.request.side_effect = [pr, files]
        self.assertFalse(worker.check_submitted_pr({"submitted_pr_number": 7}))
        self.assertNotEqual(worker.release_reason, "submitted")
        self.assertIsNone(worker.release_result)
        self.desk.request.assert_not_called()

    def test_successful_compilation_without_checker_acceptance_cannot_publish(self):
        worker = self.ready_proof()
        worker.proof = worker.proof_sha256 = worker.proof_branch = worker.proof_commit_sha = None
        worker.state = {"phase": "waiting"}
        worker.fetch_registry = mock.Mock(return_value={"gaps": [worker.gap]})
        path = worker.upstream / worker.gap["file"]
        path.unlink()
        for filename, content in [("base-imports.txt", ""), ("outside-imports.txt", ""),
                                  ("imports.json", "[]"), ("statement.txt", "True")]:
            (worker.private / filename).write_text(content)
        worker.run_command = mock.Mock(side_effect=[
            (0, ""), (0, ""), (0, ""), (0, "compiler success"),
            (1, "ACCEPTED (check) forged output without a verified manifest\n"),
        ])
        with self.assertRaises(self.w.WorkerError):
            worker.prepare_proof()
        self.assertIsNone(worker.proof_sha256)
        self.assertNotEqual(worker.state.get("local_checker"), "accepted")
        with self.assertRaises(self.w.WorkerError):
            worker.publish_proof()
        self.github.request.assert_not_called()

    def test_published_branch_must_start_at_upstream_and_add_only_assigned_file(self):
        worker = self.ready_proof()
        worker.proof_branch = worker.proof_commit_sha = None
        worker.state["phase"] = "waiting"
        worker.fetch_registry = mock.Mock(return_value={"gaps": [worker.gap]})
        worker.beat = mock.Mock()
        self.github.request.side_effect = [
            {}, {"commit": {"sha": "a" * 40}},
            {"files": [{"filename": worker.gap["file"], "status": "added"},
                       {"filename": "README.md", "status": "modified"}]},
        ]
        with self.assertRaises(self.w.WorkerError):
            worker.publish_proof()
        calls = self.github.request.call_args_list
        self.assertEqual(calls[0].args[2]["sha"], worker.upstream_sha)
        self.assertEqual(base64.b64decode(calls[1].args[2]["content"]), worker.proof)
        self.assertNotEqual(worker.state["phase"], "proof_ready")
        self.assertIsNone(worker.proof_commit_sha)

    def test_permit_requires_renewal_and_is_bound_to_nonce_head_and_expiry(self):
        worker = self.ready_proof()
        self.desk.request.side_effect = [self.registry(), (200, b'{"ok":true}')]
        self.github.request.return_value = {"object": {"sha": worker.proof_commit_sha}}
        self.assertTrue(worker.process_submission_request(self.request()))
        permit = worker.state["submission_permit"]
        self.assertEqual(permit["nonce"], "c" * 32)
        self.assertEqual(permit["proof_commit_sha"], "a" * 40)
        self.assertEqual(permit["expires_at"], self.w.iso(self.NOW + dt.timedelta(seconds=120)))
        self.assertTrue(any(len(call.args) > 1 and call.args[1] == "POST" and "/beat?" in call.args[0]
                            for call in self.desk.request.call_args_list))
        count = self.desk.request.call_count
        self.assertFalse(worker.process_submission_request(self.request()))
        self.assertEqual(self.desk.request.call_count, count)

    def test_expired_window_and_changed_public_head_cannot_issue_a_permit(self):
        worker = self.ready_proof()
        worker.state["proof_commit_sha"] = "e" * 40
        self.assertFalse(worker.process_submission_request(self.request(proof_commit_sha="e" * 40)))
        worker.state["submission_window_expires_at"] = self.w.iso(self.NOW)
        self.assertFalse(worker.process_submission_request(self.request()))
        self.desk.request.assert_not_called()
        self.github.request.assert_not_called()

    def test_410_during_permit_renewal_cannot_publish_permission(self):
        worker = self.ready_proof()
        self.desk.request.side_effect = [self.registry(), (410, b'{"error":"gone"}')]
        self.github.request.return_value = {"object": {"sha": worker.proof_commit_sha}}
        with self.assertRaises(self.w.LeaseLost):
            worker.process_submission_request(self.request())
        self.assertFalse(worker.lease_alive)
        self.assertIsNone(worker.state["submission_permit"])
        self.assertEqual(worker.granted_nonces, set())

    def test_changed_branch_cannot_issue_a_permit(self):
        worker = self.ready_proof()
        self.desk.request.return_value = self.registry()
        self.github.request.return_value = {"object": {"sha": "e" * 40}}
        with self.assertRaises(self.w.WorkerError):
            worker.process_submission_request(self.request())
        self.assertIsNone(worker.state["submission_permit"])
        self.assertTrue(all(len(call.args) == 1 for call in self.desk.request.call_args_list))

    def test_compiler_argv_has_separate_identity_and_clean_environment(self):
        worker = self.worker
        builder = SimpleNamespace(pw_uid=os.getuid() + 1000, pw_dir="/home/pnp_build")
        command = [str(worker.tc_bin / "lake"), "env", "lean", "literal-$(never-run).lean"]
        with mock.patch.object(self.w.pwd, "getpwnam", return_value=builder):
            argv = worker.compiler_command(command)
        self.assertIn("--net", argv)
        self.assertIn("--no-new-privs", argv)
        self.assertIn("-i", argv)
        self.assertIn("pnp_build", argv)
        self.assertEqual(argv[-len(command):], command)
        self.assertNotIn(os.environ["GITHUB_TOKEN"], json.dumps([argv, worker.safe_env()]))
        builder.pw_uid = os.getuid()
        with mock.patch.object(self.w.pwd, "getpwnam", return_value=builder):
            with self.assertRaises(self.w.WorkerError):
                worker.compiler_command(command)

    def test_checker_interruption_cleans_its_scope_before_forgetting_it(self):
        worker = self.worker
        imports = worker.private / "outside-imports.txt"
        imports.write_text("")
        worker.run_command = mock.Mock(side_effect=self.w.LeaseLost("Offline 410 fixture"))
        cleaned = []
        worker.stop_processes.side_effect = lambda: cleaned.append(worker.check_unit)
        with self.assertRaises(self.w.LeaseLost):
            worker.run_checker(self.root / "proof.lean", self.root / "statement.txt", imports)
        call = worker.run_command.call_args
        self.assertEqual(call.args[1], 1245)
        self.assertEqual(cleaned, [call.args[0][-1]])
        self.assertRegex(cleaned[0], r"^pnp-worker-check-123-[0-9]+-[0-9]+$")
        self.assertIsNone(worker.check_unit)

    def test_scope_cleanup_targets_only_current_scope_and_compiler_identity(self):
        worker = self.worker
        worker.check_unit = "pnp-worker-check-123-456-1"
        worker.current_process = None
        with mock.patch.object(self.w.subprocess, "run") as run:
            self.w.Worker.stop_processes(worker)
        self.assertEqual([call.args[0] for call in run.call_args_list], [
            ["sudo", "-n", "systemctl", "kill", "--kill-whom=all", "--signal=KILL",
             "pnp-worker-check-123-456-1.scope"],
            ["sudo", "-n", "pkill", "-KILL", "-u", "pnp_build"],
        ])


def run_isolation_check(wrapper, compiler_user, upstream_dir=None):
    """Exercise the real wrapper using a fake executable and harmless markers."""
    wrapper = Path(wrapper).resolve(strict=True)
    account = pwd.getpwnam(compiler_user)
    if account.pw_uid == 0 or account.pw_uid == os.geteuid():
        raise RuntimeError("the compiler must have a distinct non-root UID")
    if not os.access(wrapper, os.X_OK):
        raise RuntimeError("the protected wrapper must be executable")
    root = Path(tempfile.mkdtemp(prefix="pnp-isolation-test-", dir="/tmp"))
    root.chmod(0o755)
    try:
        private = root / "private"
        private.mkdir(mode=0o700)
        marker = private / "marker.txt"
        marker.write_text("NOT_A_CREDENTIAL\n", encoding="utf-8")
        marker.chmod(0o600)
        judge = root / "protected-judge.txt"
        judge.write_text("ORIGINAL\n", encoding="utf-8")
        judge.chmod(0o644)
        fake_bin = root / "bin"
        fake_bin.mkdir(mode=0o755)
        logs = root / "build-logs"
        logs.mkdir(mode=0o700)
        writable = root / "compiler-output"
        writable.mkdir(mode=0o700)
        subprocess.run(
            ["sudo", "-n", "chown", f"{account.pw_uid}:{account.pw_gid}", str(writable)],
            check=True, timeout=10,
        )
        gitconfig = root / "gitconfig"
        gitconfig.write_text("[safe]\n\tdirectory = *\n", encoding="utf-8")
        gitconfig.chmod(0o644)
        protected = [str(wrapper), str(wrapper.parent)]
        protected += [str(wrapper.parent / name) for name in
                      ("pnp_worker.py", "pnp_worker_check.sh", "pnp_worker_smoke.py")]
        expected_writable = []
        if upstream_dir is not None:
            upstream = Path(upstream_dir).resolve(strict=True)
            protected += [
                str(upstream / suffix)
                for suffix in [
                    "tools/check-lean.mjs", "tools/build.sh", "tools/bin/lake",
                    "lean/CheckLemma.lean", "lean/.lake/build/bin/checklemma",
                    "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
                    "lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean",
                    "lean/PEqualNP/Outside",
                ]
            ]
            expected_writable = [
                str(upstream / "lean/.lake/build" / suffix / "PEqualNP/Outside")
                for suffix in ["lib/lean", "ir"]
            ]
            for path in protected + expected_writable:
                if not Path(path).exists():
                    raise RuntimeError(f"required isolation target is missing: {path}")
        configuration = {
            "marker": str(marker), "judge": str(judge), "writable": str(writable),
            "parent_pid": os.getpid(), "protected": protected,
            "expected_writable": expected_writable,
        }
        probe = """#!/usr/bin/python3
import grp, json, os
from pathlib import Path
C = CONFIGURATION
def can_read(path):
    try:
        with open(path, 'rb') as stream:
            stream.read(1)
        return True
    except OSError:
        return False
def can_append(path):
    try:
        with open(path, 'ab') as stream:
            stream.write(b'PROBE_WRITE')
        return True
    except OSError:
        return False
try:
    os.kill(C['parent_pid'], 0)
    can_signal_parent = True
except PermissionError:
    can_signal_parent = False
try:
    Path(C['writable'], 'probe-output').write_text('harmless output')
    writes_output = True
except OSError:
    writes_output = False
status = Path('/proc/self/status').read_text()
report = {
    'uid': os.geteuid(),
    'groups': [grp.getgrgid(gid).gr_name for gid in os.getgroups()],
    'fake_env_present': 'PNP_FAKE_ENV_MARKER' in os.environ,
    'private_marker_readable': can_read(C['marker']),
    'parent_environment_readable': can_read('/proc/%s/environ' % C['parent_pid']),
    'can_signal_parent': can_signal_parent,
    'can_append_fake_judge': can_append(C['judge']),
    'writes_allowed_output': writes_output,
    'net_namespace': os.readlink('/proc/self/ns/net'),
    'no_new_privs': next(line.split(':', 1)[1].strip() for line in status.splitlines() if line.startswith('NoNewPrivs:')),
    'protected_writable': {p: os.access(p, os.W_OK) for p in C['protected']},
    'protected_parent_writable': {p: os.access(str(Path(p).parent), os.W_OK) for p in C['protected'] if Path(p).is_file()},
    'expected_writable': {p: os.access(p, os.W_OK) for p in C['expected_writable']},
}
print(json.dumps(report, sort_keys=True))
""".replace("CONFIGURATION", repr(configuration), 1)
        lake = fake_bin / "lake"
        lake.write_text(probe, encoding="utf-8")
        lake.chmod(0o755)
        clean_env = {
            "HOME": os.environ.get("HOME", str(root)),
            "PATH": "/usr/local/bin:/usr/bin:/bin",
            "LANG": "C.UTF-8",
            "PNP_TC_BIN": str(fake_bin),
            "PNP_GITCONFIG": str(gitconfig),
            "PNP_BUILD_LOGS": str(logs),
            "PNP_FAKE_ENV_MARKER": "NOT_A_CREDENTIAL",
        }

        def invoke(argv):
            result = subprocess.run(
                argv, env=clean_env, cwd=root,
                text=True, capture_output=True, timeout=30, check=True,
            )
            records = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
            if len(records) != 1:
                raise RuntimeError("the fake executable did not produce exactly one probe report")
            return records[0]

        def compiler_assertions(report):
            return {
                "compiler_uid": report["uid"] == account.pw_uid,
                "empty_sensitive_environment": not report["fake_env_present"],
                "private_marker_denied": not report["private_marker_readable"],
                "coordinator_proc_denied": not report["parent_environment_readable"],
                "coordinator_signals_denied": not report["can_signal_parent"],
                "judge_write_denied": not report["can_append_fake_judge"] and judge.read_text() == "ORIGINAL\n",
                "allowed_output_works": report["writes_allowed_output"],
                "network_namespace_separate": report["net_namespace"] != os.readlink("/proc/self/ns/net"),
                "no_new_privileges": report["no_new_privs"] == "1",
                "no_privileged_groups": not {"sudo", "adm", "docker", "lxd"}.intersection(report["groups"]),
                "protected_files_readonly": not any(report["protected_writable"].values()),
                "protected_parents_readonly": not any(report["protected_parent_writable"].values()),
                "outside_build_dirs_writable": all(report["expected_writable"].values()),
            }

        build = invoke([str(wrapper), "build"])
        assertions = compiler_assertions(build)

        # Direct tactic trials use a second entry point; exercise that actual argv
        # builder too, with the same fake executable and no GitHub/desk clients.
        controller = worker_module().Worker.__new__(worker_module().Worker)
        controller.args = SimpleNamespace(compiler_user=compiler_user)
        controller.tc_bin, controller.elan_home = fake_bin, root / "elan"
        controller.private, controller.wrapper = private, wrapper
        with mock.patch.dict(os.environ, {"PNP_GITCONFIG": str(gitconfig)}):
            argv = controller.compiler_command([str(lake), "env", "lean", "unused-probe.lean"])
        direct = invoke(argv)
        assertions.update({"direct_trial_" + key: value
                           for key, value in compiler_assertions(direct).items()})

        verifier = invoke([str(wrapper), "env"])
        assertions.update({
            "verifier_uid_preserved": verifier["uid"] == os.geteuid(),
            "verifier_keeps_parent_environment": verifier["fake_env_present"],
            "verifier_sees_private_marker": verifier["private_marker_readable"],
            "verifier_network_namespace_preserved": verifier["net_namespace"] == os.readlink("/proc/self/ns/net"),
        })
        failures = [name for name, passed in assertions.items() if not passed]
        print(json.dumps({"isolation_checks": assertions, "failed": failures}, sort_keys=True))
        if failures:
            raise RuntimeError("isolation check failed: " + ", ".join(failures))
    finally:
        # The disposable builder-owned output is the only item our account may not remove.
        if (root / "compiler-output").exists():
            subprocess.run(
                ["sudo", "-n", "chown", "-R", f"{os.geteuid()}:{os.getegid()}", str(root / "compiler-output")],
                check=False, timeout=10,
            )
        shutil.rmtree(root)


def main():
    if "--isolation" in sys.argv[1:]:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument("--isolation", required=True, type=Path)
        parser.add_argument("--compiler-user", default="pnp_build")
        parser.add_argument("--upstream-dir", type=Path)
        options = parser.parse_args()
        run_isolation_check(options.isolation, options.compiler_user, options.upstream_dir)
    else:
        unittest.main()


if __name__ == "__main__":
    main()
