# Bounded contribution worker

This worker supports the public contribution to `brilliant-hq/pequalnp-proofs` from
the `TopServeursHytale/pequalnp-proofs` fork. It is a small tactic prover and a
submission coordinator, not a general autonomous solution of P versus NP.

## Operation

The workflow runs hourly at minute 17, manually, or when its implementation is
pushed to the setup or main branch. Scheduled runs require the workflow to be on
the repository's default branch and may start later than the requested minute.
Only this public fork is eligible. A single concurrency group prevents overlapping
workers, and each run is limited to 120 minutes. The coordinator also receives a
deadline 110 minutes after preparation starts, leaving time for cleanup before
GitHub's job timeout.

Before requesting a task, the job fetches an exact upstream commit, installs
the pinned Lean toolchain, restores or downloads the pinned Mathlib, and builds
the verifier, Mathlib, and the definitions root. Outside proof sources are moved
out of the tree during that trusted build. Setup or isolation failures occur
before any reservation. Push and manual runs also require a harmless proof to
pass the real checker, under the same memory limit as a contribution. This smoke
test uses no desk task or lease; scheduled runs omit the repeated smoke test.

The worker then asks for one ordinary task. It respects an empty desk response,
tries a small set of tactics for an assigned task, and uses the project's guards
and exact checker before creating a proof branch. That branch starts at the
upstream commit and adds only the assigned Lean file. A local acceptance remains
separate from the project's authoritative verdict.

The GitHub connector creates the upstream pull request. The worker keeps the
lease private, renews it while active, grants a short submission permit after a
fresh renewal, and releases it only after it verifies the submitted pull request.
The publication wait is bounded to 90 minutes. The public state lives in
`worker-state.json` on `pnp-worker-state`; it must never contain the lease id or
an API token.

## Isolation and permissions

The only requested GitHub permission is `contents:write` on the fork. The API
token is given only to the coordinator step. There is no PAT, stored Git
credential, or token passed to a proof compilation.

The coordinator and verifier use the runner account. Every outside build uses
the separate `pnp_build` account, a fresh network namespace, an empty environment,
and `no-new-privs`. That account cannot modify the sources, verifier, toolchain,
controller, or library. Its writable build locations are restricted to the
outside-module outputs; temporary trials and its own home are also writable.
The controller and lake wrapper are installed root-owned outside the checkout.
The runner's home and private lease/log directories are inaccessible to the
compiler. Offline protocol tests and real isolation tests run before the
token-bearing step.

The verifier can need more memory than the standard runner provides. Before
locking the compiler or reserving a task, the job prepares a root-owned swap
file with mode 0600, at most 12 GiB, while preserving at least 6 GiB of disk on
that filesystem. If space is insufficient, it removes only unused preinstalled
Android, GHC, ghcup, Swift, or CodeQL toolsets from the disposable runner, stopping
as soon as sufficient space is available. It never replaces an existing swap
path. The checker runs in a separate memory-limited scope, leaving approximately
3 GiB of RAM for the coordinator and runner on the standard 16 GiB machine.
Timeouts, resource failures, and missing acceptance output block publication.
The final cleanup kills any remaining compiler processes and only the checker
scopes whose names belong to the current workflow run.

## Storage and shutdown

The workflow uses the standard `ubuntu-24.04` runner, only for the public fork.
It changes no billing settings, storage limits, security settings, or repository
secrets. The cache contains only the pinned dependency tree, is saved before
untrusted compilation, and has an 8 GiB payload ceiling. Elan and the Lean
toolchain are installed fresh on each runner, keeping the larger combined
installation out of the cache. The cache contains no proof output, state, lease,
or log. No workflow artifact is uploaded. Swap exists only for the lifetime of
the disposable runner and is not cached.

To pause future attempts, disable the `Bounded contribution worker` workflow in
GitHub Actions. Cancelling a live run may interrupt its cleanup; a lease whose
worker is lost expires normally at the desk. Never report a successful release
unless the desk actually acknowledged it.
