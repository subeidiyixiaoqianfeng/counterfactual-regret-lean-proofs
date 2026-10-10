"""Dependency-ordered local Lean checking, with explicit hash-validated resumption."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
import os
import re
import subprocess
import time

root = Path(__file__).resolve().parent
# Configure the compiler and dependency tree explicitly for this checkout.
missing = [key for key in ("DRGPR_LEAN_BIN", "DRGPR_MATHLIB_ROOT") if not os.environ.get(key)]
if missing:
    raise SystemExit("Set these environment variables first: " + ", ".join(missing))
lean = Path(os.environ["DRGPR_LEAN_BIN"]).expanduser().resolve()
math = Path(os.environ["DRGPR_MATHLIB_ROOT"]).expanduser().resolve()
if not lean.is_file():
    raise SystemExit("DRGPR_LEAN_BIN must point to a Lean 4.19.0 executable")
if not (math / ".lake/build/lib/lean").is_dir():
    raise SystemExit("DRGPR_MATHLIB_ROOT must point to a built mathlib checkout")
sources = {p.stem: p for p in root.glob("*.lean")}
deps = {n: {m for m in re.findall(r"^import\s+([\w.]+)", p.read_text("utf-8"), re.M)
            if m in sources} for n, p in sources.items()}
env = dict(os.environ)
env["LEAN_PATH"] = os.pathsep.join(map(str, [root, math / ".lake/build/lib/lean",
    *sorted((math / ".lake/packages").glob("*/.lake/build/lib/lean"))]))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
logdir = root / "fresh_audit"
logdir.mkdir(exist_ok=True)
previous_path = logdir / "BUILD.json"
previous = json.loads(previous_path.read_text("utf-8")) if previous_path.exists() else {}
if os.environ.get("DRGPR_FORCE_REBUILD") == "1":
    previous = {}
start = time.time()
report = {
    "revision": "anonymous-review-artifact",
    "all_local_modules_checked": False,
    "english_to_lean_equivalence_machine_verified": False,
    "historical_broader_claims_verified": False,
    "numbered_results_coverage": "See PAPER_COVERAGE.json, generated separately from theorem labels and checked declarations",
    "conditional_native_semantic_chain_verified": False,
    "external_controller_introduced": False,
    "base_mathlib_rebuilt_from_source": False,
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "modules": [],
}
def save():
    (logdir / "BUILD.json").write_text(json.dumps(report, indent=2), "utf-8")

def compile_one(name):
    src = sources[name]
    before = sha(src)
    proc = subprocess.run([str(lean), "-o", name + ".olean", src.name],
                          cwd=root, env=env, text=True, encoding="utf-8",
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = proc.stdout
    log = logdir / (name + ".log")
    log.write_text(out, "utf-8")
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", out, re.S)
    declarations = len(re.findall(r"^\s*(?:private\s+)?(?:theorem|lemma)\s",
                                 src.read_text("utf-8"), re.M))
    custom = re.findall(r"^\s*(?:axiom|opaque)\s", src.read_text("utf-8"), re.M)
    ax = {a.strip() for _, arr in entries for a in arr.split(",") if a.strip()}
    axiom_free = re.findall(r"'([^']+)' does not depend on any axioms", out)
    okay = (proc.returncode == 0 and "error:" not in out and "sorryAx" not in out
            and len(entries) + len(axiom_free) == declarations and not custom
            and ax <= set(report["allowed_axioms"]) and before == sha(src))
    return {"name": name, "checked": okay, "theorems": declarations,
            "source_sha256": before, "log_sha256": sha(log),
            "dependencies": sorted(deps[name])}

retained = [m for m in previous.get("modules", []) if m["checked"]
            and m["name"] in sources
            and (root / (m["name"] + ".olean")).exists()
            and sha(sources[m["name"]]) == m["source_sha256"]
            and (logdir / (m["name"] + ".log")).exists()
            and sha(logdir / (m["name"] + ".log")) == m["log_sha256"]]
done = {m["name"] for m in retained}
while any(not deps[m["name"]] <= done for m in retained):
    retained = [m for m in retained if deps[m["name"]] <= done]
    done = {m["name"] for m in retained}
assert all(deps[m["name"]] <= done for m in retained)
report["modules"] = retained
report["resumed_validated_modules"] = len(retained)
save()
running, pending = {}, set(sources) - done
with ThreadPoolExecutor(max_workers=2) as pool:
    while pending or running:
        for name in sorted(pending):
            if len(running) >= 2:
                break
            if deps[name] <= done:
                running[pool.submit(compile_one, name)] = name
                pending.remove(name)
        assert running, "Dependency cycle"
        completed, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in completed:
            name = running.pop(future)
            item = future.result()
            report["modules"].append(item)
            save()
            print(f"[{len(report['modules'])}/{len(sources)}] {name}: {item['checked']}",
                  flush=True)
            assert item["checked"], "Review " + name + ".log"
            done.add(name)
report["all_local_modules_checked"] = True
report["conditional_native_semantic_chain_verified"] = True
report["theorems"] = sum(m["theorems"] for m in report["modules"])
report["elapsed_seconds"] = round(time.time() - start, 2)
save()
print(json.dumps({k: v for k, v in report.items() if k != "modules"}, indent=2), flush=True)
