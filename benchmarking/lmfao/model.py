"""Pinned upstream query definitions; categorical features are grouping keys."""

from dataclasses import dataclass
from pathlib import Path

FIXTURES = Path(__file__).resolve().parents[2] / "benchmarks/lmfao"
COMMIT = "df6a5f59d597e9d7dd5984f268700223553789d0"


def config_lines(path: Path) -> list[str]:
    return [line.strip() for line in path.read_text().splitlines() if line.strip() and not line.startswith("#")]


@dataclass(frozen=True)
class Feature:
    name: str
    categorical: bool
    relation: str


@dataclass(frozen=True)
class Query:
    groups: tuple[str, ...] = ()
    factors: tuple[str, ...] = ()


def features() -> list[Feature]:
    lines = config_lines(FIXTURES / "features.conf")
    result = [Feature(name, kind == "1", relation) for name, kind, relation in (s.split(":") for s in lines[1:])]
    assert len(result) == int(lines[0].split(",")[0])
    return result


def schema() -> tuple[list[list[str]], dict[str, list[str]], list[list[str]]]:
    lines = config_lines(FIXTURES / "treedecomposition.conf")
    nattrs, nrels, nedges = map(int, lines[0].split())
    attrs = [line.split()[1:] for line in lines[1 : 1 + nattrs]]
    relations = {}
    for line in lines[1 + nattrs : 1 + nattrs + nrels]:
        head, columns = line.split(":")
        relations[head.split()[1]] = columns.split(",")
    edges = [line.split("-") for line in lines[1 + nattrs + nrels : 1 + nattrs + nrels + nedges]]
    return attrs, relations, edges


def queries() -> list[Query]:
    """Count, first moments, continuous squares, and all distinct feature pairs.

    Categorical features become grouping columns, as in LMFAO's generator;
    they are not incorrectly treated as numerical category codes.
    """
    # Upstream loops over attribute IDs, not the order in features.conf (whose
    # first entry names the learning label).
    by_name = {f.name: f for f in features()}
    fs = [by_name[name] for name, _ in schema()[0] if name in by_name]
    out = [Query()]
    for i, a in enumerate(fs):
        out.append(Query((a.name,), ()) if a.categorical else Query((), (a.name,)))
        if not a.categorical:
            out.append(Query((), (a.name, a.name)))
        for b in fs[i + 1 :]:
            out.append(
                Query(
                    tuple(f.name for f in (a, b) if f.categorical),
                    tuple(f.name for f in (a, b) if not f.categorical),
                )
            )
    return out
