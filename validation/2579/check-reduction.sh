#!/bin/bash
# Installed root-owned, outside the proof tree. Only the checker and its descendants
# enter this memory scope; the lease-holding Python coordinator stays outside it.
set -euo pipefail
[[ $# -eq 5 ]] || { echo 'usage: pnp_worker_check.sh UPSTREAM PROOF STATEMENT OUTSIDE_IMPORTS UNIT' >&2; exit 3; }
upstream=$1
proof=$2
statement=$3
outside_imports=$4
unit=$5
[[ $unit =~ ^pnp-worker-check-[0-9]+-[0-9]+-[0-9]+$ ]] || { echo 'invalid checker scope name' >&2; exit 3; }
[[ -d $upstream && -f $upstream/tools/check-lean.mjs && -f $proof && ! -L $proof && -f $statement && -f $outside_imports ]] || {
  echo 'required checker inputs are missing or invalid' >&2; exit 3;
}
: "${PNP_TC_BIN:?pinned toolchain bin directory}"
: "${PNP_GITCONFIG:?read-only Git configuration}"
: "${PNP_BUILD_LOGS:?private build log directory}"
: "${PEQUALNP_HOME:?build queue directory}"
: "${PEQUALNP_REAL_LAKE:?protected build wrapper}"
: "${ELAN_HOME:?prepared toolchain home}"
[[ $(id -u) -ne 0 && $(id -u) -ne $(id -u pnp_build) ]] || {
  echo 'checker must use the separate, unprivileged coordinator identity' >&2; exit 3;
}
node_bin=$(dirname "$(readlink -f "$(command -v node)")")

# Exact formula from the authoritative workflow: 3 GiB reserved on a 16 GiB
# runner, preserving the previous 6.5 GiB ceiling on an 8 GiB runner.
mem=$(awk '/^MemTotal:/{print $2}' /proc/meminfo)
old=$((mem - 1572864)); [[ $old -le 6815744 ]] || old=6815744
cap=$((mem - 3145728)); [[ $cap -ge $old ]] || cap=$old
[[ $cap -gt 0 ]] || { echo 'insufficient memory for the official checker' >&2; exit 3; }
count=$(awk 'NF {n++} END {print n+0}' "$outside_imports")
limit=$((1200 + 240 * count)); [[ $limit -le 2700 ]] || limit=2700
printf 'CHECKER_LIMITS memory_kib=%s time_seconds=%s\n' "$cap" "$limit"

cleanup() {
  code=$?
  trap - EXIT INT TERM
  # This unit contains no lease keeper, HTTP client, or GitHub token.
  sudo -n systemctl kill --kill-whom=all --signal=KILL "$unit.scope" >/dev/null 2>&1 || true
  sudo -n pkill -KILL -u pnp_build >/dev/null 2>&1 || true
  exit "$code"
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
cd "$upstream"
sudo -n systemd-run --quiet --scope --collect --unit="$unit" -p MemoryMax="${cap}K" \
  --uid="$(id -u)" --gid="$(id -g)" \
  taskset -c 0,1 env -i HOME="$HOME" LANG=C.UTF-8 \
    PATH="$PNP_TC_BIN:$node_bin:/usr/bin:/bin" ELAN_HOME="$ELAN_HOME" \
    PEQUALNP_REAL_LAKE="$PEQUALNP_REAL_LAKE" PEQUALNP_HOME="$PEQUALNP_HOME" \
    PNP_TC_BIN="$PNP_TC_BIN" PNP_GITCONFIG="$PNP_GITCONFIG" PNP_BUILD_LOGS="$PNP_BUILD_LOGS" \
    GIT_CONFIG_GLOBAL="$PNP_GITCONFIG" GIT_CONFIG_NOSYSTEM=1 LAKE_ARTIFACT_CACHE=false \
  timeout --signal=TERM --kill-after=30 "$limit" \
    node "$upstream/tools/check-lean.mjs" "$proof" "$statement" reduce
