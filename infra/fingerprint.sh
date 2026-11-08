#!/usr/bin/env bash
# The machine fingerprint (run inside a runner VM; installed in the image as rf-fingerprint; rf-job
# writes its output to /run/rf/fingerprint.json at boot, which RF_MACHINE_FINGERPRINT names for
# the jobs). Prints one JSON object with exactly these fields:
#   cpu_model         the host CPU's model name
#   vm_shape          {"vcpus": N, "memory": "M MiB"}: the slot's VM as the supervisor booted it
#   frequency_policy  a string: the canonical JSON (sorted keys, no spaces) of the pinned host CPUs'
#                     policy: cpufreq driver, amd-pstate mode, governor, EPP,
#                     scaling min/max (kHz; min = max is a fixed frequency), nominal MHz, boost
#                     (null: no boost switch on this kernel; max <= nominal keeps boost off),
#                     and `resctrl`: the L3 / memory-bandwidth partition of the bench and the others
#   image_id          sha256 of the golden image the VM booted from
#   host_kernel       the host's running kernel     } recorded, not hashed by the harness
#   microcode         the host CPU's microcode      }
# These are the types harness/rfh/bench.py fingerprint() requires (non-empty strings; vm_shape with
# an int vcpus and a memory); it hashes cpu_model, vm_shape, frequency_policy and image_id.
# The host's facts come from the VM's read-only seed (/run/rf/host.json, written by the
# supervisor; it also holds the CPU signature, QEMU's version and the pinning, for diagnosis).
# The output is the same on every boot of the same machine configuration. It fails (exit 1) if
# there is no seed, or if the guest does not see the shape the host declared.
set -euo pipefail
exec python3 -I - "${RF_HOST_JSON:-/run/rf/host.json}" <<'PY'
import json, os, sys
try:
    h = json.load(open(sys.argv[1]))
except (OSError, ValueError) as e:
    sys.exit(f"rf-fingerprint: no host facts ({e}); this VM was not booted by the supervisor")
vm = h["vm"]
shape = {"vcpus": vm["vcpus"], "memory": f"{vm['mem_mb']} MiB"}
if os.cpu_count() != shape["vcpus"]:
    sys.exit(f"rf-fingerprint: the guest sees {os.cpu_count()} vCPUs, the host declared {shape['vcpus']}")
policy = json.dumps(h["freq_policy"], sort_keys=True, separators=(",", ":"))
print(json.dumps({"cpu_model": h["cpu_model"], "vm_shape": shape, "frequency_policy": policy,
                  "image_id": h["image_id"], "host_kernel": h["host_kernel"], "microcode": h["microcode"]},
                 indent=1, sort_keys=True))
PY
