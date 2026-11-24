#!/bin/sh
# The coordinator/verifier remain separate from every untrusted lake build.
# This file is installed root-owned outside the compilable checkout.
set -eu
: "${PNP_TC_BIN:?the pinned toolchain bin directory}"
: "${PNP_GITCONFIG:?the read-only Git configuration}"

case "${1:-}" in
  build)
    log=$(mktemp -d "${PNP_BUILD_LOGS:?private build log directory}/build.XXXXXX")
    code=0
    sudo -n unshare --net -- setpriv \
      --reuid=pnp_build --regid=pnp_build --init-groups --no-new-privs \
      env -i HOME=/home/pnp_build LANG=C.UTF-8 \
        PATH="$PNP_TC_BIN:/usr/bin:/bin" \
        LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS=2 \
        GIT_CONFIG_GLOBAL="$PNP_GITCONFIG" GIT_CONFIG_NOSYSTEM=1 \
      "$PNP_TC_BIN/lake" "$@" > "$log/out" 2> "$log/err" || code=$?
    # Do not allow a tactic's descendant to survive its compilation.
    sudo -n pkill -KILL -u pnp_build || true
    printf '%s\n' "lake $* (exit $code)" > "$log/cmd"
    cat "$log/out"
    cat "$log/err" >&2
    exit "$code"
    ;;
  *)
    exec "$PNP_TC_BIN/lake" "$@"
    ;;
esac
