"""Export Slotted program sizes without collecting benchmark timings."""

from __future__ import annotations

import argparse
from pathlib import Path

from .config import DEFAULT_AST_CACHE
from .figures import DEFAULT_CONFIG, load_config, resolve_figures
from .slotted_ast import ROOT, export_slotted_ast, slotted_ast_records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "figures/output/eval")
    parser.add_argument(
        "--cache", type=Path, default=Path(DEFAULT_AST_CACHE), help="AST JSONL cache (relative to invocation)"
    )
    parser.add_argument(
        "--collect", action="store_true", help="compile missing AST identities and append them to the cache"
    )
    parser.add_argument("--compiler", type=Path, help="reuse a built slotted_ast example executable")
    args = parser.parse_args()
    (selected,) = resolve_figures(load_config(args.config), ["slotted-runtime"], Path.cwd())
    records = slotted_ast_records(selected.files, args.cache, collect=args.collect, compiler=args.compiler)
    for output in export_slotted_ast(records, args.output_dir):
        print(output)


if __name__ == "__main__":
    main()
