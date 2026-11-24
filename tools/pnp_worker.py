#!/usr/bin/env python3
"""One bounded pequalnp task, with private lease ownership and a GitHub handoff.

This controller is copied outside the compilation tree before it runs. It never
opens an upstream PR. The connected controller does that after a short-lived
submission permit; this process alone owns, renews, and releases the desk lease.
"""

import argparse
import base64
import contextlib
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import signal
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request


UPSTREAM = "brilliant-hq/pequalnp-proofs"
DESK = "https://pequalnp.com/desk"
REGISTRY = "https://data.pequalnp.com/data/desk/gaps.json"
STATE_BRANCH = "pnp-worker-state"
STATE_FILE = "worker-state.json"
SHA = re.compile(r"[0-9a-f]{40}")
MODULE = re.compile(r"PEqualNP(?:\.[A-Za-z][A-Za-z0-9_]*)+")
HEARTBEAT_SECONDS = 300
MAX_LOG_BYTES = 16 * 1024 * 1024
TACTICS = (
    ("aesop", "classical\n  aesop"),
    ("simp_all", "classical\n  intros\n  simp_all"),
    ("omega", "intros\n  omega"),
    ("exact", "exact?"),
    ("decide", "decide"),
)
PUBLIC_FIELDS = {
    "schema", "phase", "run_id", "run_url", "gap", "upstream_sha",
    "proof_branch", "proof_commit_sha", "proof_sha256", "statement_sha256",
    "local_checker", "last_lease_beat_utc", "submission_window_expires_at",
    "request_submission", "submission_permit", "submitted_pr_number",
    "submitted_pr_url", "release", "reason", "updated_at",
    "next_attempt_not_before_utc", "retry_after_s", "local_checker_log_sha256",
}


class WorkerError(Exception):
    """Messages are controlled text, never raw HTTP or compiler output."""


class LeaseLost(WorkerError):
    pass


class StopRequested(WorkerError):
    pass


class APIError(WorkerError):
    def __init__(self, status):
        self.status = status
        super().__init__(f"GitHub request failed with HTTP {status}")


def utcnow():
    return dt.datetime.now(dt.timezone.utc)


def iso(value):
    return value.astimezone(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def parse_time(value):
    if not isinstance(value, str) or len(value) > 50:
        return None
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
        return parsed.astimezone(dt.timezone.utc) if parsed.tzinfo else None
    except ValueError:
        return None


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked_json(data, label):
    if len(data) > 10 * 1024 * 1024:
        raise WorkerError(f"{label} response is too large")
    try:
        return json.loads(data)
    except (ValueError, UnicodeError, RecursionError):
        raise WorkerError(f"{label} did not return valid JSON") from None


def checker_timeout(outside_imports):
    """The authoritative job allows 20 min plus 4 per outside import, at most 45."""
    count = sum(bool(line.strip()) for line in Path(outside_imports).read_text().splitlines())
    return min(1200 + 240 * count, 2700)


def require_checker_acceptance(code, output, module, source):
    lines = output.strip().splitlines()
    manifests = [line[9:] for line in lines if line.startswith("MANIFEST ")]
    if (code or not lines or not lines[-1].startswith("ACCEPTED (check)") or len(manifests) != 1
            or any(line.startswith("REJECTED") for line in lines)):
        raise WorkerError("The exact project checker did not accept the candidate locally")
    manifest = checked_json(manifests[0].encode(), "Checker manifest")
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rests_on"), list):
        raise WorkerError("Checker manifest has an invalid shape")
    if not any(m.get("module") == module and m.get("sha256") == digest(source)
               for m in manifest["rests_on"] if isinstance(m, dict)):
        raise WorkerError("Checker manifest did not match the proof source")
    return manifest


def validate_assignment(data):
    """Return the exact gap and lease id; never include input in an exception."""
    if not isinstance(data, dict) or not isinstance(data.get("gap"), dict):
        raise WorkerError("A non-null assigned gap is required")
    lease = data.get("lease")
    lease_id = lease.get("id") if isinstance(lease, dict) else lease
    if not isinstance(lease_id, str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,200}", lease_id):
        raise WorkerError("A valid private lease id is required")
    gap = data["gap"]
    gap_id = gap.get("id")
    if not isinstance(gap_id, str) or not re.fullmatch(r"L-[a-z]+-[0-9]+", gap_id):
        raise WorkerError("Invalid assigned gap id")
    stem = gap_id.replace("-", "_")
    if gap.get("file") != f"lean/PEqualNP/Outside/{stem}.lean":
        raise WorkerError("Assigned file is not the exact allowed proof path")
    if gap.get("module") != f"PEqualNP.Outside.{stem}":
        raise WorkerError("Assigned theorem module does not match its path")
    statement = gap.get("statement")
    if not isinstance(statement, str) or not statement.strip() or "\0" in statement or len(statement.encode()) > 65536:
        raise WorkerError("Invalid exact statement")
    imports = gap.get("imports", [])
    if not isinstance(imports, list) or not all(isinstance(m, str) and MODULE.fullmatch(m) for m in imports):
        raise WorkerError("Invalid assigned imports")
    if gap.get("kind", "check") != "check":
        raise WorkerError("Only ordinary proof tasks are supported by this worker")
    if not isinstance(gap.get("title", ""), str):
        raise WorkerError("Invalid gap title")
    return gap, lease_id


def public_gap(gap):
    return {key: gap.get(key, [] if key == "imports" else "")
            for key in ("id", "title", "file", "module", "statement", "imports")}


def merge_public_state(current, patch):
    """CAS writers retain controller commands but discard unknown top-level keys."""
    merged = {key: value for key, value in current.items() if key in PUBLIC_FIELDS}
    merged.update({key: value for key, value in patch.items() if key in PUBLIC_FIELDS})
    nested = {
        "gap": {"id", "title", "file", "module", "statement", "imports"},
        "request_submission": {"nonce", "proof_commit_sha", "requested_at"},
        "submission_permit": {"nonce", "proof_commit_sha", "issued_at", "expires_at"},
        "release": {"attempted", "confirmed", "reason", "http_status", "transport_failed"},
    }
    for key, fields in nested.items():
        if isinstance(merged.get(key), dict):
            merged[key] = {name: value for name, value in merged[key].items() if name in fields}
    merged["schema"] = 1
    return merged


def validate_submission_request(command, proof_commit_sha, now):
    if not isinstance(command, dict) or not SHA.fullmatch(str(proof_commit_sha)):
        return None
    nonce, head = command.get("nonce"), command.get("proof_commit_sha")
    requested = parse_time(command.get("requested_at"))
    if (not isinstance(nonce, str) or not re.fullmatch(r"[A-Za-z0-9._-]{8,128}", nonce)
            or head != proof_commit_sha or requested is None):
        return None
    if not -30 <= (now - requested).total_seconds() <= 300:
        return None
    return {"nonce": nonce, "proof_commit_sha": head, "requested_at": iso(requested)}


def verified_pr(pr, files, repository, branch, commit_sha, gap_file, owner):
    if not isinstance(pr, dict) or not isinstance(files, list) or len(files) != 1:
        return False
    head, base = pr.get("head") or {}, pr.get("base") or {}
    return bool(
        (pr.get("state") == "open" or pr.get("merged") is True)
        and (pr.get("user") or {}).get("login") == owner
        and (head.get("repo") or {}).get("full_name") == repository
        and head.get("ref") == branch and head.get("sha") == commit_sha
        and (base.get("repo") or {}).get("full_name") == UPSTREAM and base.get("ref") == "main"
        and pr.get("changed_files") == 1
        and isinstance(files[0], dict) and files[0].get("filename") == gap_file
        and files[0].get("status") == "added"
    )


class GitHubClient:
    def __init__(self, repository, token):
        self.repository, self.token = repository, token

    def request(self, method, path, payload=None, public=False):
        if not path.startswith("/repos/"):
            raise WorkerError("Unexpected GitHub API path")
        if method != "GET" and not path.startswith(f"/repos/{self.repository}/"):
            raise WorkerError("Writes are restricted to the fork")
        headers = {"Accept": "application/vnd.github+json", "User-Agent": "pequalnp-proof-worker"}
        if not public:
            headers["Authorization"] = f"Bearer {self.token}"
        body = None if payload is None else json.dumps(payload).encode()
        request = urllib.request.Request("https://api.github.com" + path, data=body, headers=headers, method=method)
        try:
            with urllib.request.urlopen(request, timeout=20) as response:
                data = response.read(10 * 1024 * 1024 + 1)
        except urllib.error.HTTPError as exc:
            raise APIError(exc.code) from None
        except (urllib.error.URLError, TimeoutError, OSError):
            raise WorkerError("GitHub transport failed") from None
        return checked_json(data, "GitHub") if data else {}


class DeskClient:
    """Use the documented curl route; lease URLs travel on stdin, never argv."""
    def __init__(self, private_dir, sleep=time.sleep):
        self.private_dir, self.sleep, self.previous_request = Path(private_dir), sleep, 0.0

    def request(self, url, method="GET"):
        parsed = urllib.parse.urlsplit(url)
        if parsed.scheme != "https" or parsed.netloc not in {"pequalnp.com", "data.pequalnp.com"}:
            raise WorkerError("Unexpected desk destination")
        if any(c in url for c in ('"', "\n", "\r")):
            raise WorkerError("Invalid desk URL")
        delay = 3 - (time.monotonic() - self.previous_request)
        if delay > 0:
            self.sleep(min(delay, 3))
        self.previous_request = time.monotonic()
        with tempfile.NamedTemporaryFile(dir=self.private_dir, prefix="http-", delete=False) as handle:
            output = Path(handle.name)
        try:
            result = subprocess.run(
                ["curl", "--silent", "--show-error", "--connect-timeout", "10", "--max-time", "20",
                 "--max-filesize", str(10 * 1024 * 1024),
                 "--proto", "=https", "--request", method, "--config", "-",
                 "--output", str(output), "--write-out", "%{http_code}"],
                input=f'url = "{url}"\n', text=True, capture_output=True, timeout=25,
            )
            if result.returncode or not re.fullmatch(r"[0-9]{3}", result.stdout):
                raise WorkerError("Desk transport failed")
            return int(result.stdout), output.read_bytes()
        except subprocess.TimeoutExpired:
            raise WorkerError("Desk transport timed out") from None
        except OSError:
            raise WorkerError("Desk transport could not run") from None
        finally:
            output.unlink(missing_ok=True)


class StateStore:
    def __init__(self, github, repository, upstream_sha, now, sleep, secrets):
        self.github, self.repository, self.upstream_sha = github, repository, upstream_sha
        self.now, self.sleep, self.secrets = now, sleep, secrets

    def read(self):
        path = f"/repos/{self.repository}/contents/{STATE_FILE}?ref={STATE_BRANCH}"
        try:
            result = self.github.request("GET", path)
        except APIError as exc:
            if exc.status == 404:
                return {}, None
            raise
        try:
            state = checked_json(base64.b64decode(result["content"]), "Worker state")
            if not isinstance(state, dict):
                raise ValueError()
            return state, result["sha"]
        except (KeyError, ValueError, TypeError):
            raise WorkerError("Invalid public worker state") from None

    def ensure_branch(self):
        path = f"/repos/{self.repository}/git/ref/heads/{STATE_BRANCH}"
        try:
            self.github.request("GET", path)
        except APIError as exc:
            if exc.status != 404:
                raise
            try:
                self.github.request("POST", f"/repos/{self.repository}/git/refs",
                                    {"ref": f"refs/heads/{STATE_BRANCH}", "sha": self.upstream_sha})
            except APIError as create_error:
                if create_error.status != 422:
                    raise
                self.github.request("GET", path)

    def update(self, patch):
        for attempt in range(3):
            current, sha = self.read()
            merged = merge_public_state(current, {**patch, "updated_at": iso(self.now())})
            data = json.dumps(merged, ensure_ascii=False, indent=2).encode() + b"\n"
            if any(secret and secret.encode() in data for secret in self.secrets()):
                raise WorkerError("Private data was blocked from public state")
            payload = {"message": "Update bounded proof worker state", "branch": STATE_BRANCH,
                       "content": base64.b64encode(data).decode()}
            if sha:
                payload["sha"] = sha
            try:
                self.github.request("PUT", f"/repos/{self.repository}/contents/{STATE_FILE}", payload)
                return merged
            except APIError as exc:
                if exc.status not in {409, 422} or attempt == 2:
                    raise
                self.sleep(1)
        raise WorkerError("Worker state update failed")


class Worker:
    def __init__(self, args, github=None, desk=None, now=None, sleep=None):
        self.args, self.now, self.sleep = args, now or utcnow, sleep or time.sleep
        self.repository = os.environ.get("GITHUB_REPOSITORY", "")
        self.run_id = os.environ.get("GITHUB_RUN_ID", "")
        self.token = os.environ.get("GITHUB_TOKEN", "")
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", self.repository) or not self.run_id.isdigit():
            raise WorkerError("Valid GitHub repository and run id are required")
        if not self.token and github is None:
            raise WorkerError("The fork-scoped job token is required")
        self.owner = self.repository.split("/")[0]
        self.upstream = args.upstream_dir.resolve()
        self.elan_home = args.elan_home.resolve()
        private_path = os.environ.get("PNP_PRIVATE_DIR")
        self.private = Path(private_path if private_path else tempfile.mkdtemp(prefix="pnp-private-"))
        self.private.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.private.chmod(0o700)
        self.github = github or GitHubClient(self.repository, self.token)
        self.desk = desk or DeskClient(self.private, self.sleep)
        self.store = None
        self.owns_state = False
        self.state = {}
        self.gap = None
        self.lease_id = None
        self.lease_alive = False
        self.last_beat = None
        self.release_result = None
        self.release_reason = "other"
        self.stopping = False
        self.current_process = None
        self.check_unit = None
        self.process_count = 0
        self.granted_nonces = set()
        self.invalid_pr_numbers = set()
        self.proof = None
        self.proof_sha256 = None
        self.proof_branch = None
        self.proof_commit_sha = None
        self.upstream_sha = None
        self.tc_bin = Path(os.environ.get("PNP_TC_BIN", str(self.elan_home / "bin")))
        self.wrapper = Path(os.environ.get("PEQUALNP_REAL_LAKE", "/opt/pnp-controller/locked-lake.sh"))
        self.check_wrapper = Path("/opt/pnp-controller/pnp_worker_check.sh")
        self.run_deadline = parse_time(os.environ.get("PNP_RUN_DEADLINE_UTC"))

    def update(self, **patch):
        patch.update({"run_id": self.run_id, "upstream_sha": self.upstream_sha})
        if self.gap:
            patch["gap"] = public_gap(self.gap)
        if self.proof_sha256:
            patch["proof_sha256"] = self.proof_sha256
        if self.proof_branch:
            patch["proof_branch"] = self.proof_branch
        if self.proof_commit_sha:
            patch["proof_commit_sha"] = self.proof_commit_sha
        self.state = self.store.update(patch)
        return self.state

    def safe_env(self):
        return {
            "HOME": pwd.getpwuid(os.getuid()).pw_dir,
            "PATH": str(self.tc_bin) + ":/usr/local/bin:/usr/bin:/bin",
            "LANG": "C.UTF-8", "ELAN_HOME": str(self.elan_home),
            "LAKE_ARTIFACT_CACHE": "false", "LEAN_NUM_THREADS": "2",
            "PNP_TC_BIN": str(self.tc_bin),
            "PNP_GITCONFIG": os.environ.get("PNP_GITCONFIG", "/opt/pnp-work/gitconfig"),
            "GIT_CONFIG_GLOBAL": os.environ.get("PNP_GITCONFIG", "/opt/pnp-work/gitconfig"),
            "GIT_CONFIG_NOSYSTEM": "1",
            "PNP_BUILD_LOGS": os.environ.get("PNP_BUILD_LOGS", str(self.private)),
            "PEQUALNP_HOME": os.environ.get("PEQUALNP_HOME", "/opt/pnp-work/queue"),
            "PEQUALNP_REAL_LAKE": str(self.wrapper),
        }

    def compiler_command(self, command):
        user = pwd.getpwnam(self.args.compiler_user)
        if user.pw_uid in {0, os.getuid()}:
            raise WorkerError("Compiler and coordinator must have distinct unprivileged identities")
        return ["sudo", "-n", "unshare", "--net", "--", "sudo", "-n", "-u", self.args.compiler_user,
                "--", "setpriv", "--no-new-privs", "env", "-i", f"HOME={user.pw_dir}",
                f"PATH={self.tc_bin}:/usr/bin:/bin", "LANG=C.UTF-8", f"ELAN_HOME={self.elan_home}",
                "LAKE_ARTIFACT_CACHE=false", "LEAN_NUM_THREADS=2",
                "GIT_CONFIG_NOSYSTEM=1", f"GIT_CONFIG_GLOBAL={self.safe_env()['PNP_GITCONFIG']}", *command]

    def stop_processes(self):
        process = self.current_process
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except PermissionError:
                subprocess.run(["sudo", "-n", "kill", "-KILL", "--", f"-{process.pid}"],
                               capture_output=True, timeout=10)
            except ProcessLookupError:
                pass
        if self.check_unit:
            # systemd may have moved descendants outside the original process group.
            with contextlib.suppress(Exception):
                subprocess.run(["sudo", "-n", "systemctl", "kill", "--kill-whom=all", "--signal=KILL",
                                self.check_unit + ".scope"], capture_output=True, timeout=10)
        with contextlib.suppress(Exception):
            subprocess.run(["sudo", "-n", "pkill", "-KILL", "-u", self.args.compiler_user],
                           capture_output=True, timeout=10)

    def tick(self):
        if self.stopping:
            raise StopRequested("Worker termination requested")
        if self.run_deadline and self.now() >= self.run_deadline:
            self.release_reason = "out_of_time"
            raise StopRequested("The bounded runner deadline was reached")
        if self.lease_alive and (self.last_beat is None or (self.now() - self.last_beat).total_seconds() >= HEARTBEAT_SECONDS):
            self.beat()

    def run_command(self, command, timeout, compiler=False, cwd=None):
        self.tick()
        self.process_count += 1
        log = self.private / f"process-{self.process_count}.log"
        argv = self.compiler_command(["timeout", "--signal=KILL", str(timeout), *command]) if compiler else command
        with log.open("wb") as stream:
            process = subprocess.Popen(argv, cwd=cwd or self.upstream / "lean", env=self.safe_env(),
                                       stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            self.current_process = process
            deadline = time.monotonic() + timeout
            timed_out = False
            try:
                while process.poll() is None:
                    self.tick()
                    if time.monotonic() >= deadline or log.stat().st_size > MAX_LOG_BYTES:
                        timed_out = True
                        self.stop_processes()
                        break
                    self.sleep(2)
                process.wait(timeout=10)
            finally:
                if process.poll() is None or compiler:
                    self.stop_processes()
                self.current_process = None
        output = log.read_bytes()[:MAX_LOG_BYTES].decode("utf-8", errors="replace")
        return (124 if timed_out else process.returncode), output

    def run_checker(self, proof_path, statement_path, outside_imports):
        limit = checker_timeout(outside_imports)
        self.check_unit = f"pnp-worker-check-{self.run_id}-{os.getpid()}-{self.process_count + 1}"
        try:
            return self.run_command(
                [str(self.check_wrapper), str(self.upstream), str(proof_path), str(statement_path),
                 str(outside_imports), self.check_unit], limit + 45, cwd=self.upstream,
            )
        finally:
            self.stop_processes()
            self.check_unit = None

    def fetch_registry(self):
        status, body = self.desk.request(REGISTRY)
        if status != 200:
            raise WorkerError("The current desk registry could not be read")
        registry = checked_json(body, "Desk registry")
        if not isinstance(registry, dict) or not isinstance(registry.get("gaps"), list):
            raise WorkerError("The current desk registry has an invalid shape")
        return registry

    def require_matching_row(self, registry):
        rows = [row for row in registry["gaps"] if isinstance(row, dict) and row.get("id") == self.gap["id"]]
        if len(rows) != 1 or rows[0].get("kind", "check") != "check":
            raise LeaseLost("Assigned task is no longer posted as a proof task")
        paused = registry.get("paused", [])
        explicitly_paused = isinstance(paused, list) and any(
            entry == self.gap["id"] or isinstance(entry, dict) and entry.get("id") == self.gap["id"]
            for entry in paused
        )
        if rows[0].get("paused") is True or explicitly_paused:
            raise LeaseLost("Assigned task is explicitly paused on the current desk")
        for key in ("statement", "module", "file", "imports"):
            default = [] if key == "imports" else None
            if rows[0].get(key, default) != self.gap.get(key, default):
                raise LeaseLost("Assigned task changed before publication")

    def beat(self):
        if not self.lease_alive or not self.lease_id:
            raise LeaseLost("No live lease is available")
        status, body = self.desk.request(DESK + "/beat?" + urllib.parse.urlencode({"lease": self.lease_id}), "POST")
        if status == 410:
            self.lease_alive = False
            self.stop_processes()
            raise LeaseLost("The desk returned 410; all work and publication stopped")
        response = checked_json(body, "Lease heartbeat")
        if status != 200 or not isinstance(response, dict) or response.get("ok") is False or response.get("error"):
            raise WorkerError("The lease heartbeat was not confirmed")
        self.last_beat = self.now()
        if self.store:
            self.update(last_lease_beat_utc=iso(self.last_beat))

    def release(self, reason):
        if not self.lease_alive or not self.lease_id or self.release_result is not None:
            return self.release_result
        result = {"attempted": True, "confirmed": False, "reason": reason}
        try:
            status, body = self.desk.request(DESK + "/release?" + urllib.parse.urlencode({"lease": self.lease_id, "reason": reason}), "POST")
            result["http_status"] = status
            if 200 <= status < 300:
                response = checked_json(body, "Lease release")
                result["confirmed"] = isinstance(response, dict) and response.get("ok") is not False and not response.get("error")
            if result["confirmed"] or status == 410:
                self.lease_alive = False
        except WorkerError:
            result["transport_failed"] = True
        self.release_result = result
        return result

    def acquire(self):
        if self.run_deadline and (self.run_deadline - self.now()).total_seconds() < 1200:
            self.update(phase="blocked", reason="Insufficient runner time remains to take a lease")
            return False
        status, join = self.desk.request("https://pequalnp.com/join.txt")
        if status != 200 or not join.strip():
            raise WorkerError("Current participation instructions could not be read")
        (self.private / "join.txt").write_bytes(join)
        self.fetch_registry()
        if self.run_deadline and (self.run_deadline - self.now()).total_seconds() < 1200:
            self.update(phase="blocked", reason="Insufficient runner time remains to take a lease")
            return False
        status, body = self.desk.request(DESK + "/next?" + urllib.parse.urlencode({"handle": self.owner}))
        if status != 200:
            raise WorkerError("Task allocation was not successful")
        assigned = checked_json(body, "Task allocation")
        if not isinstance(assigned, dict):
            raise WorkerError("Task allocation has an invalid shape")
        if assigned.get("gap") is None:
            retry = assigned.get("retry_after_s", 300)
            if isinstance(retry, bool) or not isinstance(retry, (int, float)) or not 1 <= retry <= 86400:
                retry = 300
            self.update(phase="waiting", reason="No task assigned; no lease held", retry_after_s=retry,
                        next_attempt_not_before_utc=iso(self.now() + dt.timedelta(seconds=retry)))
            return False
        lease = assigned.get("lease")
        lease_id = lease.get("id") if isinstance(lease, dict) else lease
        if isinstance(lease_id, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,200}", lease_id):
            self.lease_id, self.lease_alive = lease_id, True
            print("::add-mask::" + lease_id, flush=True)
            (self.private / "assignment.json").write_bytes(body)
            (self.private / "assignment.json").chmod(0o600)
        self.gap, _ = validate_assignment(assigned)
        self.last_beat = self.now()
        self.update(gap=public_gap(self.gap), last_lease_beat_utc=iso(self.last_beat),
                    statement_sha256=digest(self.gap["statement"].encode()), phase="waiting", reason="Working on one assigned task")
        weight = self.gap.get("weight", 1)
        if (self.gap.get("hard") is True or not isinstance(weight, (int, float)) or weight > 1
                or "shard" in assigned or "SEARCH" in self.gap.get("title", "").upper()):
            self.update(phase="finished", reason="Assigned task is outside the bounded tactic worker's capabilities")
            return False
        self.beat()
        return True

    def prepare_proof(self):
        registry = self.fetch_registry()
        self.require_matching_row(registry)
        registry_path = self.private / "gaps.json"
        registry_path.write_text(json.dumps(registry), encoding="utf-8")
        guard = self.upstream / ".github/scripts/outside-guard.mjs"
        proof_path = self.upstream / self.gap["file"]
        if proof_path.exists() or proof_path.is_symlink():
            raise WorkerError("The assigned proof path already exists")
        commands = [
            ["node", str(guard), "gap", str(registry_path), self.gap["id"], self.gap["file"], str(self.private), "check"],
            ["node", str(guard), "closure", str(self.upstream), str(self.private / "imports.json"),
             self.gap["file"], str(self.private), "check"],
        ]
        for command in commands:
            code, _ = self.run_command(command, 20, cwd=self.upstream)
            if code:
                raise WorkerError("The current gap or import closure guard refused the assignment")
        for filename, isolated in (("base-imports.txt", False), ("outside-imports.txt", True)):
            modules = (self.private / filename).read_text().splitlines()
            if modules:
                code, _ = self.run_command([str(self.tc_bin / "lake"), "build", *["+" + m for m in modules]], 900, compiler=isolated)
                if code:
                    raise WorkerError("Required project imports could not be built")
        header = "import Mathlib\n" + "".join(f"import {m}\n" for m in self.gap.get("imports", []))
        header += "\nset_option maxHeartbeats 200000 in\nset_option maxRecDepth 2048 in\n"
        for _, tactic in TACTICS:
            self.tick()
            source = (header + f"theorem {self.gap['module']} : {self.gap['statement']} := by\n  {tactic}\n").encode()
            proof_path.write_bytes(source)
            proof_path.chmod(0o644)
            command = ["node", str(guard), "imports", str(proof_path), str(self.private / "imports.json"), self.gap["file"], "check"]
            code, _ = self.run_command(command, 20, cwd=self.upstream)
            if code:
                raise WorkerError("Generated proof file failed the current plain-file guard")
            code, _ = self.run_command([str(self.tc_bin / "lake"), "env", "lean", str(proof_path)], 30, compiler=True)
            if proof_path.read_bytes() != source:
                raise WorkerError("Proof source changed during compilation")
            if code:
                continue
            code, output = self.run_checker(proof_path, self.private / "statement.txt", self.private / "outside-imports.txt")
            require_checker_acceptance(code, output, self.gap["module"], source)
            if proof_path.read_bytes() != source:
                raise WorkerError("Proof source changed after checking")
            self.proof = source
            self.proof_sha256 = digest(source)
            self.update(proof_sha256=self.proof_sha256, local_checker="accepted",
                        local_checker_log_sha256=digest(output.encode()))
            return True
        self.update(phase="finished", reason="No candidate proved the assigned statement within the bounded tactic attempts")
        return False

    def verify_proof_unchanged(self):
        if not self.proof or digest(self.proof) != self.proof_sha256:
            raise WorkerError("The validated proof bytes are unavailable")
        if (self.upstream / self.gap["file"]).read_bytes() != self.proof:
            raise WorkerError("The validated proof file changed")
        if self.proof_branch:
            ref = self.github.request("GET", f"/repos/{self.repository}/git/ref/heads/{self.proof_branch}")
            if (ref.get("object") or {}).get("sha") != self.proof_commit_sha:
                raise WorkerError("The public proof branch changed after validation")

    def publish_proof(self):
        if self.state.get("local_checker") != "accepted" or self.proof_sha256 is None:
            raise WorkerError("Publication requires exact local checker acceptance")
        self.require_matching_row(self.fetch_registry())
        self.beat()
        self.verify_proof_unchanged()
        window_end = self.now() + dt.timedelta(minutes=self.args.max_wait_minutes)
        if self.run_deadline:
            window_end = min(window_end, self.run_deadline - dt.timedelta(seconds=60))
        if (window_end - self.now()).total_seconds() < 120:
            self.release_reason = "out_of_time"
            raise WorkerError("Insufficient runner time remains for a submission handoff")
        branch = f"pnp-proof-{self.gap['id'].lower()}-{self.run_id}"
        self.github.request("POST", f"/repos/{self.repository}/git/refs",
                            {"ref": "refs/heads/" + branch, "sha": self.upstream_sha})
        response = self.github.request("PUT", f"/repos/{self.repository}/contents/{self.gap['file']}",
            {"branch": branch, "message": self.gap["id"], "content": base64.b64encode(self.proof).decode(),
             "committer": {"name": "github-actions[bot]", "email": "41898282+github-actions[bot]@users.noreply.github.com"},
             "author": {"name": "github-actions[bot]", "email": "41898282+github-actions[bot]@users.noreply.github.com"}})
        commit = (response.get("commit") or {}).get("sha")
        if not isinstance(commit, str) or not SHA.fullmatch(commit):
            raise WorkerError("GitHub did not confirm the proof commit")
        comparison = self.github.request("GET", f"/repos/{self.repository}/compare/{self.upstream_sha}...{commit}")
        files = comparison.get("files") or []
        if len(files) != 1 or files[0].get("filename") != self.gap["file"] or files[0].get("status") != "added":
            raise WorkerError("Published proof branch does not add exactly the assigned file")
        self.proof_branch, self.proof_commit_sha = branch, commit
        self.update(phase="proof_ready", reason="Validated locally; waiting for the connected controller to submit the PR",
                    proof_branch=branch, proof_commit_sha=commit,
                    submission_window_expires_at=iso(window_end), submission_permit=None)
        self.verify_proof_unchanged()

    def process_submission_request(self, public_state):
        request = validate_submission_request(public_state.get("request_submission"), self.proof_commit_sha, self.now())
        if request is None or request["nonce"] in self.granted_nonces:
            return False
        deadline = parse_time(self.state.get("submission_window_expires_at"))
        if not self.lease_alive or self.state.get("phase") != "proof_ready" or deadline is None or self.now() >= deadline:
            return False
        self.tick()
        self.require_matching_row(self.fetch_registry())
        self.verify_proof_unchanged()
        self.beat()
        self.verify_proof_unchanged()
        issued = self.now()
        if issued >= deadline:
            return False
        permit = {"nonce": request["nonce"], "proof_commit_sha": request["proof_commit_sha"],
                  "issued_at": iso(issued), "expires_at": iso(min(deadline, issued + dt.timedelta(seconds=120)))}
        self.update(submission_permit=permit)
        self.granted_nonces.add(request["nonce"])
        return True

    def check_submitted_pr(self, public_state):
        number = public_state.get("submitted_pr_number")
        if isinstance(number, bool) or not isinstance(number, int) or not 1 <= number <= 10**12 or number in self.invalid_pr_numbers:
            return False
        try:
            pr = self.github.request("GET", f"/repos/{UPSTREAM}/pulls/{number}", public=True)
            files = self.github.request("GET", f"/repos/{UPSTREAM}/pulls/{number}/files?per_page=2", public=True)
        except APIError as exc:
            if exc.status != 404:
                raise
            self.invalid_pr_numbers.add(number)
            return False
        if not verified_pr(pr, files, self.repository, self.proof_branch,
                           self.proof_commit_sha, self.gap["file"], self.owner):
            self.invalid_pr_numbers.add(number)
            return False
        self.release_reason = "submitted"
        result = self.release("submitted")
        self.update(phase="submitted", submitted_pr_url=f"https://github.com/{UPSTREAM}/pull/{number}",
                    submission_permit=None, release=result, reason="Upstream pull request verified; official verdict pending")
        return True

    def wait_for_submission(self):
        deadline = parse_time(self.state["submission_window_expires_at"])
        while self.now() < deadline:
            self.tick()
            public_state, _ = self.store.read()
            if public_state.get("run_id") != self.run_id:
                raise WorkerError("Another controller replaced this run's public state")
            if self.check_submitted_pr(public_state):
                return
            self.process_submission_request(public_state)
            self.sleep(15)
        self.release_reason = "out_of_time"
        self.update(phase="finished", submission_permit=None,
                    reason="Submission window expired without a verified pull request acknowledgement")

    def run(self):
        os.umask(0o077)
        try:
            code, output = self.run_command(["git", "rev-parse", "HEAD"], 10, cwd=self.upstream)
            self.upstream_sha = output.strip()
            if code or not SHA.fullmatch(self.upstream_sha):
                raise WorkerError("Pinned upstream commit could not be established")
            self.store = StateStore(self.github, self.repository, self.upstream_sha, self.now, self.sleep,
                                    lambda: (self.token, self.lease_id))
            self.store.ensure_branch()
            current, _ = self.store.read()
            next_attempt = parse_time(current.get("next_attempt_not_before_utc"))
            if next_attempt and self.now() < next_attempt:
                print("Worker deferred: the desk's retry delay has not elapsed", flush=True)
                return 0
            old_beat = parse_time(current.get("last_lease_beat_utc"))
            if (current.get("run_id") != self.run_id and current.get("phase") in {"waiting", "proof_ready"}
                    and old_beat and 0 <= (self.now() - old_beat).total_seconds() < 1200):
                raise WorkerError("Another worker still has a recent live-lease heartbeat")
            self.update(phase="waiting", run_id=self.run_id,
                        run_url=f"https://github.com/{self.repository}/actions/runs/{self.run_id}",
                        upstream_sha=self.upstream_sha, gap=None, proof_branch=None, proof_commit_sha=None,
                        proof_sha256=None, statement_sha256=None, local_checker=None, last_lease_beat_utc=None,
                        submission_window_expires_at=None, submission_permit=None, submitted_pr_url=None,
                        request_submission=None, submitted_pr_number=None,
                        release=None, next_attempt_not_before_utc=None, retry_after_s=None,
                        local_checker_log_sha256=None, reason="Environment prepared; requesting at most one ordinary task")
            self.owns_state = True
            if self.acquire() and self.prepare_proof():
                self.publish_proof()
                self.wait_for_submission()
            return 0
        except WorkerError as exc:
            self.stop_processes()
            if self.store and self.owns_state:
                with contextlib.suppress(WorkerError):
                    self.update(phase="blocked", reason=str(exc), submission_permit=None)
            print("Worker stopped: " + str(exc), flush=True)
            return 1
        except Exception as exc:
            self.stop_processes()
            reason = "Unexpected internal failure: " + type(exc).__name__
            if self.store and self.owns_state:
                with contextlib.suppress(Exception):
                    self.update(phase="blocked", reason=reason, submission_permit=None)
            print(reason, flush=True)
            return 1
        finally:
            self.stop_processes()
            result = self.release(self.release_reason)
            if self.store and self.owns_state and result is not None:
                with contextlib.suppress(WorkerError):
                    self.update(release=result, submission_permit=None)
            for name in ("assignment.json",):
                (self.private / name).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-dir", type=Path, required=True)
    parser.add_argument("--elan-home", type=Path, required=True)
    parser.add_argument("--compiler-user", default="pnp_build")
    parser.add_argument("--max-wait-minutes", type=int, default=90)
    args = parser.parse_args()
    if not 1 <= args.max_wait_minutes <= 120 or not re.fullmatch(r"[a-z_][a-z0-9_-]*", args.compiler_user):
        parser.error("Invalid bounded waiting period or compiler user")
    try:
        worker = Worker(args)
    except WorkerError as exc:
        print("Worker setup failed: " + str(exc), file=sys.stderr)
        return 1
    def stop(_signum, _frame):
        worker.stopping = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    return worker.run()


if __name__ == "__main__":
    sys.exit(main())
