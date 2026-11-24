#!/usr/bin/env bash
# Bootstrap only on a disposable GitHub-hosted runner, before acquiring a lease.
set -euo pipefail
umask 022

readonly work_root=/opt/pnp-work
readonly controller_root=/opt/pnp-controller
readonly upstream_dir="$work_root/upstream"
readonly elan_home="$work_root/elan"
readonly compiler_user=pnp_build
readonly elan_version=4.4.0
readonly elan_archive_sha=0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2

fail() { printf 'SETUP FAULT: %s\n' "$*" >&2; exit 1; }
[[ ${GITHUB_ACTIONS:-} == true ]] || fail 'this bootstrap is only for a disposable GitHub Actions runner'
[[ ${GITHUB_REPOSITORY:-} == TopServeursHytale/pequalnp-proofs ]] || fail 'unexpected repository'
[[ -z ${GITHUB_TOKEN:-} && -z ${GH_TOKEN:-} ]] || fail 'do not give an API token to the bootstrap'
: "${RUNNER_TEMP:?}" "${GITHUB_ENV:?}" "${GITHUB_OUTPUT:?}"
readonly coordinator_user=$(id -un)
readonly coordinator_group=$(id -gn)
readonly private_dir="$RUNNER_TEMP/pnp-private"

available_bytes() { df -B1 --output=avail "$work_root" | awk 'NR==2 { print $1 }'; }

case "${1:-}" in
  prepare)
    [[ $HOME == /home/runner ]] || fail 'unexpected runner home; refusing to change its access'
    chmod 0700 "$HOME"
    sudo -n install -d -m 0755 -o "$coordinator_user" -g "$coordinator_group" "$work_root"
    [[ $(available_bytes) -ge 12884901888 ]] || fail 'less than 12 GiB free before restoring or installing Lean'
    sudo -n install -d -m 0755 -o root -g root "$controller_root"
    if ! id "$compiler_user" >/dev/null 2>&1; then
      sudo -n useradd --system --create-home --home-dir /home/pnp_build --shell /usr/sbin/nologin "$compiler_user"
    fi
    [[ $(id -u "$compiler_user") != $(id -u) ]] || fail 'compiler and coordinator must have different UIDs'
    sudo -n chmod 0700 /home/pnp_build
    # The compiler cannot read the coordinator's private lease or log directory.
    install -d -m 0700 "$private_dir" "$private_dir/builds"
    for item in pnp_worker.py test_pnp_worker.py pnp_worker_smoke.py pnp_worker_check.sh; do
      [[ -f "tools/$item" ]] || fail "missing controller source tools/$item"
      sudo -n install -m 0755 -o root -g root "tools/$item" "$controller_root/$item"
    done
    sudo -n install -m 0755 -o root -g root tools/pnp_worker_setup.sh "$controller_root/setup.sh"
    sudo -n install -m 0755 -o root -g root tools/pnp_worker_locked_lake.sh "$controller_root/locked-lake.sh"
    [[ ! -e $upstream_dir ]] || fail 'the upstream snapshot directory already exists'
    git init -q "$upstream_dir"
    GIT_TERMINAL_PROMPT=0 git -C "$upstream_dir" -c credential.helper= fetch -q --depth 1 \
      https://github.com/brilliant-hq/pequalnp-proofs.git refs/heads/main
    git -C "$upstream_dir" checkout -q --detach FETCH_HEAD
    upstream_sha=$(git -C "$upstream_dir" rev-parse HEAD)
    [[ $upstream_sha =~ ^[0-9a-f]{40}$ ]] || fail 'invalid upstream commit'
    git -C "$upstream_dir" config core.hooksPath /dev/null
    mkdir -p "$elan_home" "$upstream_dir/lean/.lake/packages" "$work_root/queue"
    printf '1\n' > "$work_root/queue/build-slots.conf"
    printf '2\n' > "$work_root/queue/build-jobs.conf"
    printf '[safe]\n\tdirectory = %s\n' "$upstream_dir" > "$work_root/gitconfig"
    chmod 0644 "$work_root/gitconfig"
    pin_key=$(python3 - "$upstream_dir" <<'PY'
import hashlib, pathlib, sys
root = pathlib.Path(sys.argv[1]) / 'lean'
h = hashlib.sha256(b'elan4.4.0\0')
for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
    h.update(name.encode() + b'\0' + (root / name).read_bytes() + b'\0')
print(h.hexdigest())
PY
    )
    printf 'pin_key=%s\nupstream_sha=%s\n' "$pin_key" "$upstream_sha" >> "$GITHUB_OUTPUT"
    {
      printf 'PNP_UPSTREAM_DIR=%s\n' "$upstream_dir"
      printf 'PNP_UPSTREAM_SHA=%s\n' "$upstream_sha"
      printf 'PNP_ELAN_HOME=%s\n' "$elan_home"
      printf 'PNP_PRIVATE_DIR=%s\n' "$private_dir"
      printf 'PNP_BUILD_LOGS=%s\n' "$private_dir/builds"
      printf 'PNP_TRIAL_DIR=%s\n' "$work_root/trials"
      printf 'PNP_GITCONFIG=%s\n' "$work_root/gitconfig"
      printf 'PEQUALNP_HOME=%s\n' "$work_root/queue"
      python3 - <<'PY'
import datetime
deadline = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(minutes=110)
print('PNP_RUN_DEADLINE_UTC=' + deadline.isoformat())
PY
    } >> "$GITHUB_ENV"
    printf 'Prepared upstream commit %s; no task has been reserved.\n' "$upstream_sha"
    ;;

  build)
    [[ -d $upstream_dir/.git ]] || fail 'prepare must run first'
    export ELAN_HOME="$elan_home"
    current_elan=$({ "$elan_home/bin/elan" --version || true; } 2>/dev/null)
    if [[ $current_elan != "elan $elan_version "* && $current_elan != "elan $elan_version" ]]; then
      installer_dir=$(mktemp -d "$RUNNER_TEMP/pnp-elan.XXXXXX")
      curl -fsSL --retry 2 --connect-timeout 20 --max-time 180 \
        "https://github.com/leanprover/elan/releases/download/v$elan_version/elan-x86_64-unknown-linux-gnu.tar.gz" \
        -o "$installer_dir/elan.tar.gz"
      printf '%s  %s\n' "$elan_archive_sha" "$installer_dir/elan.tar.gz" | sha256sum --check --status
      tar -xzf "$installer_dir/elan.tar.gz" -C "$installer_dir" elan-init
      "$installer_dir/elan-init" -y --no-modify-path --default-toolchain none
      rm -rf -- "$installer_dir"
    fi
    toolchain=$(tr -d '\r\n' < "$upstream_dir/lean/lean-toolchain")
    [[ $toolchain =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9.]+)?$ ]] || fail 'unsupported toolchain pin'
    "$elan_home/bin/elan" toolchain install "$toolchain"
    cd "$upstream_dir/lean"
    tc_bin=$(dirname "$("$elan_home/bin/elan" which lake)")
    tc_bin=$(readlink -f "$tc_bin")
    [[ $tc_bin == "$elan_home/toolchains/"* ]] || fail 'toolchain escaped the prepared directory'
    [[ -x $tc_bin/lake && -x $tc_bin/lean ]] || fail 'pinned binaries are missing'
    export PATH="$tc_bin:/usr/local/bin:/usr/bin:/bin"
    export PEQUALNP_REAL_LAKE="$tc_bin/lake" PEQUALNP_HOME="$work_root/queue" LAKE_ARTIFACT_CACHE=false
    [[ ! -e lakefile.lean ]] || fail 'unexpected root lakefile.lean'
    "$tc_bin/lake" exe cache get
    git diff --quiet HEAD -- lakefile.toml lake-manifest.json lean-toolchain || fail 'a pinned configuration changed'
    # No outside-written proof may run before the compiler sandbox is ready.
    aside="$work_root/outside-during-bootstrap"
    mkdir "$aside"
    restore_outside() {
      if [[ -d $aside/Outside ]]; then
        [[ ! -e PEqualNP/Outside && ! -L PEqualNP/Outside ]] || fail 'an Outside directory appeared during trusted setup'
        mv "$aside/Outside" PEqualNP/Outside
      fi
    }
    trap restore_outside EXIT
    if [[ -d PEqualNP/Outside ]]; then mv PEqualNP/Outside "$aside/Outside"; fi
    ../tools/bin/lake build checklemma +Mathlib +PEqualNP.Defs
    restore_outside
    trap - EXIT
    rmdir "$aside"
    for outside_build in .lake/build/lib/lean/PEqualNP/Outside .lake/build/ir/PEqualNP/Outside; do
      if [[ -d $outside_build ]] && find "$outside_build" -type f -print -quit | grep -q .; then
        fail 'trusted setup unexpectedly compiled an outside module'
      fi
    done
    [[ -x .lake/build/bin/checklemma ]] || fail 'the verifier was not built'
    [[ -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]] || fail 'the full Mathlib cache is missing'
    git diff --quiet HEAD -- lakefile.toml lake-manifest.json lean-toolchain || fail 'a pinned configuration changed during setup'
    printf 'PNP_TC_BIN=%s\n' "$tc_bin" >> "$GITHUB_ENV"
    cache_bytes=$(du -sb "$upstream_dir/lean/.lake/packages" | awk '{print $1}')
    # One payload is capped at 8 GiB. The repository's existing cache quota is not changed.
    if [[ $cache_bytes -le 8589934592 ]]; then
      printf 'cache_ok=true\n' >> "$GITHUB_OUTPUT"
    else
      printf 'cache_ok=false\n' >> "$GITHUB_OUTPUT"
      printf 'Cache save skipped: prepared payload exceeds 8 GiB.\n'
    fi
    printf 'Prepared Lean/Mathlib and verifier; cache payload %s bytes.\n' "$cache_bytes"
    ;;

  swap)
    [[ ${RUNNER_ENVIRONMENT:-} == github-hosted && $HOME == /home/runner ]] || fail 'swap preparation requires the disposable GitHub-hosted runner'
    [[ -x $upstream_dir/lean/.lake/build/bin/checklemma ]] || fail 'prepared verifier missing'
    readonly reserve_bytes=6442450944
    readonly max_swap_bytes=12884901888
    select_swap_location() {
      swap_parent=''
      swap_available=0
      for candidate in / /mnt; do
        [[ -d $candidate && ! -L $candidate ]] || continue
        [[ $(readlink -f -- "$candidate") == "$candidate" ]] || continue
        [[ $(stat -c %u -- "$candidate") == 0 ]] || continue
        mode=$(stat -c %a -- "$candidate")
        [[ $mode =~ ^[0-7]{3,4}$ ]] || fail 'invalid swap parent permissions'
        (( (8#$mode & 0022) == 0 )) || continue
        free=$(df -B1 --output=avail "$candidate" | awk 'NR==2 { print $1 }')
        [[ $free =~ ^[0-9]+$ ]] || fail 'could not measure swap filesystem space'
        if (( free > swap_available )); then
          swap_parent=$candidate
          swap_available=$free
        fi
      done
      [[ -n $swap_parent ]] || fail 'no protected swap location is available'
    }
    select_swap_location
    # Reclaim only these unused toolsets from the upstream workflow, and only
    # while the selected filesystem cannot hold 12 GiB plus the 6 GiB reserve.
    for toolset in /usr/local/lib/android /opt/ghc /usr/local/.ghcup /usr/share/swift /opt/hostedtoolcache/CodeQL; do
      (( swap_available < reserve_bytes + max_swap_bytes )) || break
      case "$toolset" in
        /usr/local/lib/android|/opt/ghc|/usr/local/.ghcup|/usr/share/swift|/opt/hostedtoolcache/CodeQL) ;;
        *) fail 'refusing an unexpected toolset cleanup path' ;;
      esac
      [[ -e $toolset || -L $toolset ]] || continue
      [[ -d $toolset && ! -L $toolset && $(readlink -f -- "$toolset") == "$toolset" ]] || fail 'toolset cleanup path is not a fixed real directory'
      ! mountpoint -q -- "$toolset" || fail 'refusing to remove a mounted toolset'
      printf 'Reclaiming unused runner toolset: %s\n' "$toolset"
      sudo -n rm -rf --one-file-system -- "$toolset"
      select_swap_location
    done
    # Round down to full MiB, preserving at least 6 GiB for the actual work.
    swap_bytes=$(( (swap_available - reserve_bytes) / 1048576 * 1048576 ))
    (( swap_bytes <= max_swap_bytes )) || swap_bytes=$max_swap_bytes
    (( swap_bytes >= 1073741824 )) || fail 'not enough space for 1 GiB swap with 6 GiB disk kept free'
    swap_file="${swap_parent%/}/pnp-worker-swap"
    case "$swap_file" in
      /pnp-worker-swap|/mnt/pnp-worker-swap) ;;
      *) fail 'refusing an unexpected swap path' ;;
    esac
    [[ ! -e $swap_file && ! -L $swap_file ]] || fail 'refusing to replace an existing swap path'
    sudo -n install -m 0600 -o root -g root /dev/null "$swap_file"
    sudo -n fallocate -l "$swap_bytes" "$swap_file"
    [[ $(stat -c '%u:%g:%a' -- "$swap_file") == 0:0:600 ]] || fail 'swap ownership or permissions are incorrect'
    sudo -n mkswap -q "$swap_file"
    sudo -n swapon -- "$swap_file"
    remaining=$(df -B1 --output=avail "$swap_parent" | awk 'NR==2 { print $1 }')
    (( remaining >= reserve_bytes )) || fail 'less than 6 GiB disk remains after allocating swap'
    printf 'Verifier swap: %s MiB at %s; %s bytes remain free.\n' "$((swap_bytes / 1048576))" "$swap_file" "$remaining"
    free -m
    ;;

  lock)
    : "${PNP_TC_BIN:?build must run first}"
    [[ -x $upstream_dir/lean/.lake/build/bin/checklemma ]] || fail 'prepared verifier missing'
    sudo -n pkill -KILL -u "$compiler_user" || true
    # Upstream sources and trusted build outputs are writable by the coordinator,
    # never by the account that elaborates an outside proof.
    chmod -R a+rX,go-w "$upstream_dir" "$elan_home" "$work_root/queue"
    for output in lib/lean ir; do
      directory="$upstream_dir/lean/.lake/build/$output/PEqualNP/Outside"
      mkdir -p "$directory"
      chmod 0755 "$directory"
      sudo -n chown "$compiler_user:$compiler_user" "$directory"
    done
    sudo -n install -d -m 0755 -o "$compiler_user" -g "$compiler_user" "$work_root/trials"
    chmod 0700 "$private_dir" "$private_dir/builds"
    chmod 0700 "$HOME"
    chmod 0644 "$work_root/gitconfig"
    [[ $(available_bytes) -ge 2147483648 ]] || fail 'less than 2 GiB free after preparation'
    printf 'Locked compiler access. No task has been reserved.\n'
    ;;

  *)
    fail 'usage: pnp_worker_setup.sh prepare|build|swap|lock'
    ;;
esac
