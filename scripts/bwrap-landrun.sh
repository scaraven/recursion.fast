#!/usr/bin/env bash
# A filesystem sandbox with landrun's command line, for the comparator (TRUSTED harness tool; v3's
# shim, A6-G0, hardened for v4 by V4-A1). The comparator calls
#   landrun --best-effort --ro / --rw /dev -ldd -add-exec [--env V]... [--ro P]... [--rwx P]... [--rox P]... -- CMD ARGS
# for the solution's `lake build` and for `lean4export`. This shim maps it to bubblewrap:
#   - minimal root (the default when RF_LANDRUN_MINIMAL=1, as `harness/evaluate.py` sets it, or with
#     `--minimal-root` as the first option): an empty root holding /usr (and its /bin, /lib, /lib64,
#     /sbin links), a fresh /tmp, the `--ro`/`--rox` paths except `/`, and the colon-separated paths
#     of RF_LANDRUN_RO (the toolchain, the organiser checkout, the package tree); otherwise the whole
#     file system read-only (`--ro-bind / /`), v3's behaviour;
#   - only the `--rw`/`--rwx` paths are writable (for `lake build`, the fresh tree's `.lake`);
#   - a fresh /dev and /proc; no network; new user (no further user namespaces), pid, ipc and uts
#     namespaces, so every process the elaboration starts dies with the command
#     (`--die-with-parent`); a new session; all capabilities dropped;
#   - the seccomp filter of `harness/rfh/sandbox.py` (ptrace, process_vm_*, bpf, perf_event_open,
#     userfaultfd, io_uring, keyrings, mounts, namespaces, module loading fail with EPERM);
#   - the environment cleared except the `--env` variables (landrun semantics);
#   - `--hide PATH` (an extension): PATH is invisible inside (a tmpfs over a directory, /dev/null over
#     a file).
# Executability restrictions (`--rox`) are not modelled (bwrap has no per-path exec bit).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
MIN=${RF_LANDRUN_MINIMAL:-0}; [[ "${1:-}" == --minimal-root ]] && { MIN=1; shift; }
if [[ $MIN == 1 ]]; then
  args=(--ro-bind /usr /usr --tmpfs /tmp)
  for l in bin lib lib64 sbin; do
    if [[ -L "/$l" ]]; then args+=(--symlink "$(readlink "/$l")" "/$l"); elif [[ -d "/$l" ]]; then args+=(--ro-bind "/$l" "/$l"); fi
  done
  [[ -e /etc/ld.so.cache ]] && args+=(--ro-bind /etc/ld.so.cache /etc/ld.so.cache)
  IFS=: read -r -a extra <<< "${RF_LANDRUN_RO:-}"
  for p in "${extra[@]}"; do [[ -n "$p" && -e "$p" ]] && args+=(--ro-bind "$p" "$p"); done
else
  args=(--ro-bind / /)
fi
args+=(--dev /dev --proc /proc --unshare-user --disable-userns --unshare-net --unshare-pid --unshare-ipc
      --unshare-uts --die-with-parent --new-session --clearenv --cap-drop ALL)
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    --rw|--rwx) [[ "$2" == /dev ]] || args+=(--bind "$2" "$2"); shift 2 ;;
    --ro|--rox) if [[ $MIN == 1 && "$2" != / ]]; then args+=(--ro-bind "$2" "$2"); fi; shift 2 ;;   # else already readable
    --hide) if [[ -d "$2" ]]; then args+=(--tmpfs "$2"); else args+=(--ro-bind /dev/null "$2"); fi; shift 2 ;;
    --env) if [[ -v "$2" ]]; then args+=(--setenv "$2" "${!2}"); fi; shift 2 ;;
    --bind-tcp|--connect-tcp|--log-level) shift 2 ;;
    -*) shift ;;                           # --best-effort, -ldd, -add-exec, ...
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo "bwrap-landrun: no command" >&2; exit 2; }
[[ $MIN == 1 ]] && args+=(--remount-ro /)
sc=$(mktemp); trap 'rm -f "$sc"' EXIT
python3 -I -c "import sys; sys.path.insert(0, sys.argv[1]); from rfh.sandbox import seccomp_program; sys.stdout.buffer.write(seccomp_program())" \
  "$HERE/../harness" > "$sc"
exec 9< "$sc"; rm -f "$sc"; trap - EXIT
exec bwrap "${args[@]}" --seccomp 9 -- "$@"
