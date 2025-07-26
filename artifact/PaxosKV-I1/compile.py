import os
import json
import sys

base_dir = os.path.dirname(os.path.abspath(__file__))

config_path = os.path.join(base_dir, "../config.json")

try:
	with open(config_path, "r") as f:
		data = json.load(f)
		dafny_path = os.path.normpath(os.path.join(base_dir, data["dafny_path"]))
		nthreads = data["nthreads_to_compile"]
except FileNotFoundError:
	print(f"[✗] config.json not found at: {config_path}")
	sys.exit(1)
except Exception as e:
	print(f"[✗] Failed to load config.json: {e}")
	sys.exit(1)

success_flag = os.path.join(base_dir, "ironfleet", "build_success.flag")
if os.path.exists(success_flag):
	os.remove(success_flag)
	print("[*] Removed old success flag.")

ironfleet_dir = os.path.join(base_dir, "ironfleet")
cmd = f"cd {ironfleet_dir} && time scons -j {nthreads} --dafny-path={dafny_path}"
print("[+] Running build command:")
print(f"    {cmd}")
ret = os.system(cmd)

# if ret == 0:
# 	print("[✓] Build finished (exit code 0)")
# else:
# 	print(f"[✗] Build failed (exit code {ret})")
