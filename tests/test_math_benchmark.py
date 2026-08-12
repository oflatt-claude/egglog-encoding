"""Test the generated fixed Math comparison workload."""

from __future__ import annotations

import subprocess
import sys

from benchmarking.engines import MATH_EGG_WORKLOAD
from scripts import generate_math_benchmark


def test_math_fixture_matches_the_generator_and_egg_mapping() -> None:
    subprocess.run(
        [sys.executable, str(generate_math_benchmark.ROOT / "scripts/generate_math_benchmark.py"), "--check"],
        cwd=generate_math_benchmark.ROOT,
        check=True,
    )

    source = generate_math_benchmark.OUTPUT_PATH.read_text(encoding="utf-8")
    assert source == generate_math_benchmark.render_math()
    assert source.count("(run)") == generate_math_benchmark.ITERATIONS == MATH_EGG_WORKLOAD.iterations
    assert "(run 10)" not in source
    assert "run-with" not in source
    assert "back-off" not in source
    assert generate_math_benchmark.EGGLOG_CHECK_LEFT in source
    assert generate_math_benchmark.EGGLOG_CHECK_RIGHT in source
    assert MATH_EGG_WORKLOAD.check_left == generate_math_benchmark.EGG_CHECK_LEFT
    assert MATH_EGG_WORKLOAD.check_right == generate_math_benchmark.EGG_CHECK_RIGHT
