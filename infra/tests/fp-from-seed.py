#!/usr/bin/env python3
"""The fingerprint hash a VM will compute, from its seed (root, on the host): reads rf-host.json
from the seed ISO (isoinfo), maps it as infra/fingerprint.sh does and hashes it as
harness/rfh/bench.py fingerprint() does.   fp-from-seed.py SEED.ISO"""
import hashlib, json, subprocess, sys
raw = subprocess.run(["isoinfo", "-R", "-i", sys.argv[1], "-x", "/rf-host.json"], capture_output=True, check=True).stdout
h = json.loads(raw)
fp = {"cpu_model": h["cpu_model"], "vm_shape": {"vcpus": h["vm"]["vcpus"], "memory": f"{h['vm']['mem_mb']} MiB"},
      "frequency_policy": json.dumps(h["freq_policy"], sort_keys=True, separators=(",", ":")), "image_id": h["image_id"]}
canon = json.dumps(fp, sort_keys=True, separators=(",", ":"))
print(hashlib.sha256(canon.encode()).hexdigest(), "rf-host.json sha256", hashlib.sha256(raw).hexdigest())
