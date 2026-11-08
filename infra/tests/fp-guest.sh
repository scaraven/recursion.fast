# The machine fingerprint as the harness hashes it (rf-test SLOT fp-guest.sh): the canonical JSON
# (sort_keys, separators "," ":") of cpu_model, vm_shape, frequency_policy, image_id of the file at
# RF_MACHINE_FINGERPRINT (the formula of harness/rfh/bench.py fingerprint()), and the file's sha256.
python3 -I - <<'PY'
import hashlib, json, os
p = os.environ["RF_MACHINE_FINGERPRINT"]; raw = open(p, "rb").read(); o = json.loads(raw)
canon = json.dumps({k: o[k] for k in ("cpu_model", "vm_shape", "frequency_policy", "image_id")}, sort_keys=True, separators=(",", ":"))
print("FP-HASH", hashlib.sha256(canon.encode()).hexdigest(), "file-sha256", hashlib.sha256(raw).hexdigest())
PY
