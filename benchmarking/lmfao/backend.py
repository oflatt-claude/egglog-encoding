"""Compile selected views with the pinned LMFAO backend and check all outputs."""

from __future__ import annotations

import math
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any

from . import model
from .data import Results

FLAGS = "-std=c++11 -O3 -pthread -mtune=native -ftree-vectorize -fopenmp"


def command(
    args: list[str], directory: Path, log: str, *, env: dict[str, str] | None = None, timeout: int = 300
) -> float:
    start = time.perf_counter()
    try:
        result = subprocess.run(
            args, cwd=directory, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=timeout
        )
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        (directory / log).write_bytes(error.output or b"")
        raise RuntimeError(f"{args[0]} failed; see {directory / log}") from error
    elapsed = time.perf_counter() - start
    (directory / log).write_bytes(result.stdout)
    return elapsed


def prepare(
    compiler: Path,
    data: Path,
    directory: Path,
    plan: Path | None,
    *,
    flags: str = FLAGS,
    jobs: int = 4,
    timeout: int = 300,
) -> dict[str, Any]:
    directory.mkdir(parents=True, exist_ok=True)
    # An inherited import variable must not contaminate the original control.
    env = dict(os.environ)
    env.pop("LMFAO_PLAN_FILE", None)
    if plan is not None:
        env["LMFAO_PLAN_FILE"] = str(plan.resolve())
    generated = command(
        [
            str(compiler),
            "--path",
            str(data),
            "--model",
            "covar",
            "--parallel",
            "none",
            "--mo",
            "1",
            "--compress",
            "1",
            "--out",
            str(directory),
        ],
        directory,
        "generate.log",
        env=env,
        timeout=timeout,
    )
    if plan is not None and "LMFAO imported selected DAG:" not in (directory / "generate.log").read_text():
        raise ValueError("backend did not acknowledge plan import; install the pinned adapter")
    built = command(["make", f"-j{jobs}", "CXX=g++", "CXXFLAG=" + flags], directory, "build.log", timeout=timeout)
    return {
        "generation_seconds": generated,
        "compilation_seconds": built,
        "compiler_counts": (directory / "compiler-data.out").read_text(),
        "flags": flags,
        "logical_optimizer": "original LMFAO" if plan is None else "bypassed; imported selected egraph DAG",
    }


def validate(directory: Path, expected: Results, *, flags: str = FLAGS, timeout: int = 300) -> dict[str, Any]:
    """Use a separate diagnostic executable; preserve the timed objects/binary."""
    source = (directory / "main.cpp").read_text()
    needle = "void dumpOutputViews()\n   {\n      std::ofstream ofs;"
    if source.count(needle) != 1:
        raise ValueError("pinned backend dump function changed")
    (directory / "main-dump.cpp").write_text(source.replace(needle, needle + "\n      ofs << std::setprecision(17);"))
    import shlex

    options = shlex.split(flags)
    command(
        ["g++", *options, "-DDUMP_OUTPUT", "-include", "iomanip", "-c", "main-dump.cpp", "-o", "main-dump.o"],
        directory,
        "build-dump-main.log",
        timeout=timeout,
    )
    command(
        ["g++", *options, "-DDUMP_OUTPUT", "-c", "ApplicationHandler.cpp", "-o", "application-dump.o"],
        directory,
        "build-dump-application.log",
        timeout=timeout,
    )
    target = next(line for line in (directory / "Makefile").read_text().splitlines() if line.startswith("lmfao :"))
    objects = [
        {"main.o": "main-dump.o", "application.o": "application-dump.o"}.get(name, name)
        for name in target.split(":", 1)[1].split()
    ]
    command(["g++", *options, *objects, "-o", "lmfao-dump"], directory, "link-dump.log", timeout=timeout)
    (directory / "output").mkdir(exist_ok=True)
    command(
        [str(directory / "lmfao-dump")],
        directory,
        "validate.log",
        env={**os.environ, "OMP_NUM_THREADS": "1"},
        timeout=timeout,
    )
    mapping = [
        tuple(map(int, line.split(",")))
        for line in (directory / "output/covarianceMatrix.out").read_text().splitlines()
    ]
    if len(mapping) != len(expected):
        raise AssertionError("missing query outputs")
    worst = 0.0
    for i, (view, aggregate) in enumerate(mapping):
        lines = (directory / f"output/V{view}.tbl").read_text().splitlines()
        keys, columns = map(int, lines[0].split())
        if keys != len(model.queries()[i].groups) or aggregate >= columns:
            raise AssertionError("query output shape differs")
        got = {}
        for line in lines[1:]:
            values = line.split("|")
            key = tuple(map(int, values[:keys]))
            if len(values) != keys + columns or key in got:
                raise AssertionError("malformed or duplicate output row")
            got[key] = float(values[keys + aggregate])
        want = {tuple(r[:-1]): float(r[-1]) for r in expected[i]}
        if got.keys() != want.keys():
            raise AssertionError((i, "group keys differ"))
        for key, value in want.items():
            equal = (
                math.isclose(got[key], value, rel_tol=1e-9, abs_tol=1e-7)
                if model.queries()[i].factors
                else got[key] == value
            )
            if not equal:
                raise AssertionError((i, key, got[key], value))
            worst = max(worst, abs(got[key] - value) / max(1, abs(value)))
    return {
        "queries_checked": len(expected),
        "counts_and_keys": "exact",
        "max_scaled_error": worst,
        "relative_tolerance": 1e-9,
        "absolute_tolerance": 1e-7,
    }


def execute(directory: Path, repeat: int, timeout: int) -> dict[str, float]:
    elapsed = command(
        [str(directory / "lmfao")],
        directory,
        f"run-{repeat}.log",
        env={**os.environ, "OMP_NUM_THREADS": "1"},
        timeout=timeout,
    )
    log = (directory / f"run-{repeat}.log").read_text()
    matches = re.findall(r"^Data process: ([0-9]+)ms\.$", log, re.MULTILINE)
    if len(matches) != 1:
        raise ValueError("missing upstream computation-time report")
    return {"process_seconds": elapsed, "computation_seconds": int(matches[0]) / 1000}
