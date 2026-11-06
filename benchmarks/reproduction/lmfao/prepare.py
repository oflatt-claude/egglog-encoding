"""Build the optimizer bridge in a separate checkout of the pinned LMFAO commit."""

import argparse
import shutil
import subprocess
from pathlib import Path

from benchmarking.lmfao.model import COMMIT


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True, help="Existing LMFAO git checkout")
    parser.add_argument("--output", type=Path, required=True, help="New checkout/build directory")
    parser.add_argument("--boost", type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    out = args.output.resolve()
    source = out / "source"
    adapter = Path(__file__).resolve().parent
    if out.exists():
        parser.error("--output must be a new directory")
    out.mkdir(parents=True)
    subprocess.run(["git", "-C", str(args.source), "worktree", "add", "--detach", str(source), COMMIT], check=True)
    subprocess.run(["git", "-C", str(source), "apply", str(adapter / "optimizer-bridge.patch")], check=True)
    subprocess.run(["git", "-C", str(source), "apply", str(adapter / "dependent-output.patch")], check=True)
    for header in ("ImportPlan.hpp", "OptimizerBridge.hpp"):
        shutil.copy2(adapter / header, source / "src/compiler" / header)
    cmake = ["cmake", "-S", str(source), "-B", str(out / "build")]
    if args.boost:
        boost = args.boost.resolve()
        cmake += [
            f"-DBOOST_ROOT={boost}",
            f"-DBOOST_LIBRARYDIR={boost}/lib/x86_64-linux-gnu",
            "-DBoost_NO_SYSTEM_PATHS=ON",
            "-DBoost_NO_BOOST_CMAKE=ON",
            f"-DCMAKE_CXX_FLAGS=-I{boost}/include",
        ]
    subprocess.run(cmake, check=True)
    subprocess.run(["cmake", "--build", str(out / "build"), f"-j{args.jobs}"], check=True)


if __name__ == "__main__":
    main()
