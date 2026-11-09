"""Export Slotted program sizes without collecting benchmark timings."""

from __future__ import annotations

import argparse
from pathlib import Path

from .figures import DEFAULT_CONFIG, load_config, resolve_figures
from .slotted_ast import ROOT, export_slotted_ast


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "figures/output/eval")
    parser.add_argument("--compiler", type=Path, help="reuse a built slotted_ast example executable")
    args = parser.parse_args()
    (selected,) = resolve_figures(load_config(args.config), ["slotted-runtime"], Path.cwd())
    for output in export_slotted_ast(selected.files, args.output_dir, compiler=args.compiler):
        print(output)


if __name__ == "__main__":
    main()
