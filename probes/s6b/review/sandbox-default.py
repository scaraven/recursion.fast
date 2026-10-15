import importlib.util, json, tempfile
spec = importlib.util.spec_from_file_location("rb", "harness/run-benchmark.py")
rb = importlib.util.module_from_spec(spec); spec.loader.exec_module(rb)
cfgpath = tempfile.mktemp(suffix=".json")
# A board-L config that OMITS "sandbox":
json.dump({"k":24,"boards":["L"],"verify":["/bin/true"],"index":["/bin/true"],
           "prover":["/bin/true"],"gen":"g"}, open(cfgpath,"w"))
cfg = rb.load_config(cfgpath)
print("board-L config, 'sandbox' key omitted -> cfg['sandbox'] =", repr(cfg["sandbox"]))
print("Runner.run: 'if sb:' guard is", "FALSE (unsandboxed: no --hide, no bwrap, network/FS open)" if not cfg["sandbox"] else "true")
# secrets hiding only happens inside 'if sb:' -> with None the secrets file and workdir are NOT hidden
