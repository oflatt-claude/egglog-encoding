#!/usr/bin/env python3
"""One independent spot check: paper array example N=0, eight rules, six rounds.

Uses the normal slotted CLI and reference binary, but no eval/xdiff Python modules.
Builds release binaries first; times each process once, including a graph dump.
Compare with slotted-eval.py's array N=0 / ref-multi rows: same input, rules, atom order,
and budget. This check omits slotted-eval.py's goal observation and isomorphism check.
"""

import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# The same input in each language. The encoding reads the eight source rules;
# their explicit MultiPattern translations below are intentionally easy to inspect.
SOURCE = """
(include "slotted/languages/array-rules.egg")
(let input
  (Lam $1000 (Lam $1001 (Lam $1002 (Lam $1003
    (App (Sym "map") (App (Sym "map")
      (Lam $100 (App $1003 (App $1002 (App $1001 (App $1000 $100))))))))))))
(run 6)

"""

REFERENCE = """
rounds 6
sizes
ctor app App
ctor lam Lam
ctor let Let
ctor number Num
ctor symbol Sym
term (lam $1000 (lam $1001 (lam $1002 (lam $1003 (app map (app map (lam $100 (app (var $1003) (app (var $1002) (app (var $1001) (app (var $1000) (var $100))))))))))))

# eta
rule
atom _p lam $x _t1
atom _sl1 var $x
atom _t1 app f _sl1
rhs _p ?f
cond notin $x f

# let-intro
rule
atom _p app _t1 e
atom _t1 lam $x body
rhs _p (let $x ?body ?e)

# let-unused
rule
atom _p let $x b e
rhs _p ?b
cond notin $x b

# let-var-same
rule
atom _sl1 var $x
atom _p let $x _sl1 e
rhs _p ?e

# let-app
rule
atom _p let $x _t1 e
atom _t1 app a b
rhs _p (app (let $x ?a ?e) (let $x ?b ?e))
cond in $x a b

# let-lam-diff
rule
atom _p let $x _t1 e
atom _t1 lam $y body
rhs _p (lam $y (let $x ?body ?e))
cond notin $y e
cond in $x body

# map-fusion
rule
atom _p app _t1 _t2
atom _cl1 map
atom _t1 app _cl1 f
atom _t2 app _t3 arg
atom _cl2 map
atom _t3 app _cl2 g
rhs _p (app (app map (lam $fu (app ?f (app ?g (var $fu))))) ?arg)

# map-fission
rule
atom _cl1 map
atom _p app _cl1 _t1
atom _t1 lam $x _t2
atom _t2 app f gx
rhs _p (lam $in (app (app map ?f) (app (app map (lam $x ?gx)) (var $in))))
cond notin $x f
"""  # noqa: E501

# After maintenance, each live constructor row is a node and its e-class is the
# slotted leader. Count these directly from JSON, ignoring auxiliary tables.
CONSTRUCTORS = {"SlottedVar_0", "Lam", "App", "Let", "Sym", "Num"}


def run(command: list[str], source: str | None = None) -> tuple[str, float]:
    start = time.perf_counter()
    result = subprocess.run(
        command,
        input=source,
        cwd=ROOT,
        env={**os.environ, "XMULTI_SUBST": "snapshot"},
        capture_output=True,
        text=True,
        timeout=300,
    )
    elapsed = time.perf_counter() - start
    if result.returncode:
        sys.exit(result.stderr or result.stdout)
    return result.stdout, elapsed


def main() -> None:
    subprocess.run(["cargo", "build", "--release", "-p", "egglog-experimental"], cwd=ROOT, check=True)
    subprocess.run(
        ["cargo", "build", "--release", "--no-default-features", "--manifest-path", "slotted/xmulti/Cargo.toml"],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="slotted-spot-") as directory:
        source = Path(directory) / "input.egg"
        source.write_text(SOURCE)
        _, enc_seconds = run(
            [
                str(ROOT / "target/release/egglog-experimental"),
                "--slotted",
                "--to-json",
                "--max-functions",
                "10000",
                "--max-calls-per-function",
                "1000000",
                str(source),
            ]
        )
        nodes = json.loads(source.with_suffix(".json").read_text())["nodes"].values()
        rows = [node for node in nodes if node["op"] in CONSTRUCTORS]
        enc_sizes = len({node["eclass"] for node in rows}), len(rows)
        ref, ref_seconds = run([str(ROOT / "slotted/xmulti/target/release/xmulti")], REFERENCE)

    assert "CONFIG checks=off" in ref and "CONFIG substitution=snapshot" in ref, ref
    [sizes] = [line.split()[1:] for line in ref.splitlines() if line.startswith("SIZES ")]
    ref_sizes = tuple(map(int, sizes))
    print("Array N=0, 6 rounds; one process run each, build excluded; egglog includes transformation and JSON dump")
    print(f"{'System':<14} {'Classes':>8} {'Nodes':>8} {'Seconds':>10}")
    for label, (classes, nodes), seconds in (
        ("egglog", enc_sizes, enc_seconds),
        ("ref-multi", ref_sizes, ref_seconds),
    ):
        print(f"{label:<14} {classes:>8} {nodes:>8} {seconds:>10.4f}")
    print("Sizes match." if enc_sizes == ref_sizes else "SIZES DIFFER.")
    sys.exit(0 if enc_sizes == ref_sizes else 1)


if __name__ == "__main__":
    main()
