#!/usr/bin/env python3
"""Campaign failures and empty coverage must propagate to the exit status."""

import contextlib
import io
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "xdiff"))
import campaign as C  # noqa: E402


def main():
    cases = [
        (0, [(1000, 0, "1/1 isomorphic")]),
        (1, [(1000, 1, "1/1 isomorphic")]),
        (1, [(1000, 1, "Traceback: worker crashed")]),
        (1, [(1000, 0, "no summary")]),
        (1, [(1000, 0, "0/0 isomorphic (1 ran out of time)")]),
        (1, [(1000, 0, "0/1 isomorphic")]),
        (1, [(1000, 0, "1/1 isomorphic"), (1001, 1, "worker crashed")]),
        # Limits remain explicitly reported coverage gaps when some cases compared.
        (0, [(1000, 0, "  limit fuzz1 reference timeout\n1/1 isomorphic (1 ran out of time)")]),
    ]
    for want, results in cases:
        argv = ["campaign.py", "iso", "--cases", "2", "--seeds", str(len(results)), "--jobs", "1"]
        with (
            patch.object(sys, "argv", argv),
            patch.object(C, "run_seed", side_effect=results),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            assert C.main() == want, results
    with patch.object(C.subprocess, "run", return_value=subprocess.CompletedProcess([], 7, "out", "err")):
        assert C.run_seed(Path("worker.py"), [], 2, 1000) == (1000, 7, "outerr")
    print("OK: campaign exit status rejects worker failures, missing summaries, and empty coverage")


if __name__ == "__main__":
    main()
