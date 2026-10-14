#!/usr/bin/env bash
# A real filesystem sandbox with landrun's command line, for hosts without landrun (A6-G0).
# The comparator calls `landrun --best-effort --ro / --rw /dev -ldd -add-exec [--env V]... [--ro P]...
# [--rwx P]... [--rox P]... -- CMD ARGS`. This shim maps it to bubblewrap:
#   - the whole file system is read-only (`--ro-bind / /`); only the `--rw`/`--rwx` paths are
#     writable (for `lake build` that is the fresh tree's `.lake`, never the organiser package,
#     the toolchain or the shared packages: those are outside it, so a solution build cannot
#     rewrite a trusted `.olean`, cf. probes/a6-probes/cmpproj scenario B);
#   - a fresh /dev and /proc; no network (`--unshare-net`); own PID namespace, so every process the
#     solution's elaboration starts (`#eval`, `IO.Process.spawn`, daemons) is killed when the command
#     exits (`--unshare-pid --die-with-parent`); new session (no TIOCSTI);
#   - the environment is cleared except the `--env` variables (landrun semantics).
# Executability restrictions (`--rox`) are not modelled (bwrap has no per-path exec bit).
set -euo pipefail
args=(--ro-bind / / --dev /dev --proc /proc --unshare-net --unshare-pid --unshare-ipc --unshare-uts
      --die-with-parent --new-session --clearenv)
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    --rw|--rwx) [[ "$2" == /dev ]] || args+=(--bind "$2" "$2"); shift 2 ;;
    --ro|--rox) shift 2 ;;                 # already readable
    --env) if [[ -v "$2" ]]; then args+=(--setenv "$2" "${!2}"); fi; shift 2 ;;
    --bind-tcp|--connect-tcp|--log-level) shift 2 ;;
    -*) shift ;;                           # --best-effort, -ldd, -add-exec, ...
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo "bwrap-landrun: no command" >&2; exit 2; }
exec bwrap "${args[@]}" -- "$@"
