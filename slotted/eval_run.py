"""Build and time the two executables. Graph export and checking live in eval_verify."""

import os
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path

from benchmarking.reports.slotted import workload_label

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "target" / "slotted"

#: Release builds of both sides: egglog, and the reference through `xmulti` without the
#: crate's `checks` feature, the way the paper's experiments ran it.
EGGLOG = ROOT / "target" / "release" / "egglog-experimental"
#: `--group-cap`: how many live slots the oracle enumerates a symmetry group over when it
#: dumps its graph; past it the exact comparison is unavailable, but direct counts remain.
#: The oracle's own default is 6. Larger SDQL graphs exceed even 10; raising the
#: cap has factorial cost, so keep counts available independently of that limit.
GROUP_CAP = 10
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "release" / "xmulti"
BUILDS = (
    ("cargo", "build", "--release", "-p", "egglog-experimental"),
    ("cargo", "build", "--release", "--no-default-features", "--manifest-path", "slotted/xmulti/Cargo.toml"),
)


@dataclass(frozen=True)
class Config:
    egglog: Path = EGGLOG
    xmulti: Path = XMULTI
    group_cap: int = GROUP_CAP


def quiet_progress(row, phase):
    """Library callers collect observations without displaying CLI progress."""


class Progress:
    """One dot per sample; identify a phase only when it takes more than five seconds.

    Timer callbacks only print to stderr. Cancel and join before changing the display
    so a completed phase cannot report itself as still running.
    """

    delay = 5

    def __init__(self, parallel=False):
        self.timer = None
        self.workload = None
        self.line_open = False
        self.parallel = parallel

    def __enter__(self):
        return self

    def cancel(self):
        if self.timer is not None:
            self.timer.cancel()
            self.timer.join()
            self.timer = None

    def __exit__(self, *_):
        self.cancel()
        if self.line_open:
            print(file=sys.stderr, flush=True)

    def __call__(self, row, phase):
        self.cancel()
        if phase == "idle":
            return
        label = workload_label(row.study, row.case, row.rules)
        if self.parallel and phase == "done":
            print(".", end="", file=sys.stderr, flush=True)
            return
        if not self.parallel and row.workload() != self.workload:
            if self.line_open:
                print(file=sys.stderr)
            print(f"{label}: ", end="", file=sys.stderr, flush=True)
            self.workload, self.line_open = row.workload(), True
        if phase == "done":
            print("." if self.line_open else "  .", end="", file=sys.stderr, flush=True)
            self.line_open = True
            return

        def slow():
            if self.parallel:
                # Write a complete, short message at once so workers' text does not
                # interleave inside a message. Dots may arrive between messages.
                sys.stderr.write(f"\n  {label} / {row.side}: {phase} (Running ...)\n")
                sys.stderr.flush()
                return
            if self.line_open:
                print(file=sys.stderr)
            print(f"  {label} / {row.side}: {phase} (Running ...)", file=sys.stderr, flush=True)
            self.line_open = False

        self.timer = threading.Timer(self.delay, slow)
        self.timer.daemon = True
        self.timer.start()


def build(*, env=None):
    """Bring both binaries up to date, so a timing is of the code in the checkout.
    cargo's own output stays on stderr."""
    for cmd in BUILDS:
        subprocess.run(cmd, cwd=ROOT, stdout=sys.stderr, env=env, check=True)


def oracle_env(side, group_cap):
    """Use the selected substitution policy without reference debugging overhead."""
    return {
        **{
            key: value
            for key, value in os.environ.items()
            if key not in ("XMULTI_DEBUG", "XMULTI_DEBUG_RULE", "XMULTI_TRACE")
        },
        "XMULTI_GROUP_SLOT_CAP": str(group_cap),
        "XMULTI_SUBST": "syntactic" if side == "ref-nested" else "snapshot",
    }


def run_reference(spec, row, timeout, progress=quiet_progress, *, config=None):
    """Time the reference goal check with an explicit substitution policy."""
    config = config or Config()
    env = oracle_env(row.side, config.group_cap)
    row.substitution = env["XMULTI_SUBST"]
    progress(row, "goal")
    t0 = time.perf_counter()
    try:
        r = subprocess.run([str(config.xmulti)], input=spec, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        row.graph_issue = "reference timed run exceeded timeout"
        return
    row.seconds = time.perf_counter() - t0
    lines = r.stdout.splitlines()
    if r.returncode != 0 and "REFERENCE_LIMIT:" not in r.stderr:
        row.goal = "error: " + ((r.stderr.strip().splitlines() or ["?"])[-1])[:80]
        row.graph_issue = row.goal
        return
    row.goal = next((ln.split()[1] for ln in lines if ln.startswith("GOAL ")), "?")
    row.saturated = next((ln.split()[1] for ln in lines if ln.startswith("SATURATED ")), "?")
    row.checks = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG checks=")), None)
    reported_subst = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG substitution=")), None)
    if reported_subst != row.substitution:
        row.goal = "error: reference substitution policy missing or unexpected; rebuild xmulti"
        row.graph_issue = row.goal
        return


def slotted_flags(row):
    return ["--slotted", *(["--slotted-no-aliasing"] if row.side == "encoding-no-aliasing" else [])]


def goal_result(result):
    if result.returncode == 0:
        return "yes"
    return "no" if "Check failed" in result.stderr else "error"


def run_egglog(program, name, row, timeout, progress=quiet_progress, *, config=None):
    """Time source transformation, execution, and the goal check in one process."""
    config = config or Config()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}.egg"
    path.write_text(program)
    progress(row, "goal")
    t0 = time.perf_counter()
    try:
        r = subprocess.run(
            [str(config.egglog), *slotted_flags(row), str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        return
    finally:
        path.unlink(missing_ok=True)
    row.seconds = time.perf_counter() - t0
    row.goal = goal_result(r)
