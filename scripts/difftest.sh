#!/usr/bin/env bash
# Differentially test the Lean semantics against egglog.
#
# `difftest` (semantics/DiffTest.lean) writes one .egg file and one .expected file per
# case; each .expected holds the per-constructor row counts the Lean interpreter predicts.
# This runs egglog on the .egg file and diffs its `(print-size)` output against that.
#
# Row counts are the same quantity egglog/tests/files.rs snapshots: one row per distinct
# canonical argument tuple, which on the Lean side is one per congruence class of
# argument lists.
#
# Cases come in two kinds. The curated ones are the Redex test.rkt programs plus
# variations, and are only as good as whoever chose them. The random ones are generated
# from seeds, which is what removes that bias. RANDOM_CASES sets how many.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
out="${DIFFTEST_OUT:-$root/.difftest}"
egglog="${EGGLOG_BIN:-$root/target/release/egglog}"
random_cases="${RANDOM_CASES:-60}"
# A generated program can blow up in either engine; cap both rather than hang the run.
per_case_timeout="${DIFFTEST_TIMEOUT:-20}"

if [[ ! -x "$egglog" ]]; then
  echo "difftest: no egglog binary at $egglog" >&2
  echo "difftest: build one with 'cargo build --release -p egglog', or set EGGLOG_BIN" >&2
  exit 1
fi

export PATH="$HOME/.elan/bin:$PATH"
cd "$root/semantics" || exit 1
lake build difftest >/dev/null || exit 1
gen=".lake/build/bin/difftest"

rm -rf -- "$out"
mkdir -p -- "$out"

"$gen" "$out" curated >/dev/null || exit 1
skipped=0
for ((i = 0; i < random_cases; i++)); do
  if ! timeout "$per_case_timeout" "$gen" "$out" seed "$i" >/dev/null 2>&1; then
    rm -f -- "$out/rand-$i".*
    skipped=$((skipped + 1))
  fi
done

fail=0
pass=0
for egg in "$out"/*.egg; do
  name="$(basename "$egg" .egg)"
  # `(print-size)` prints `((Add 2)\n (One 1))`; reduce to sorted `name count` lines.
  if ! timeout "$per_case_timeout" "$egglog" "$egg" >"$out/$name.raw" 2>"$out/$name.err"; then
    echo "FAIL $name: egglog failed or timed out"
    sed 's/^/      /' "$out/$name.err" | head -5
    fail=$((fail + 1))
    continue
  fi
  tr -d '()' <"$out/$name.raw" | awk 'NF==2 {print $1, $2}' | sort >"$out/$name.actual"
  sort <"$out/$name.expected" >"$out/$name.want"
  if diff -q "$out/$name.want" "$out/$name.actual" >/dev/null; then
    pass=$((pass + 1))
  else
    echo "FAIL $name: row counts differ (want = Lean, actual = egglog)"
    sed 's/^/      /' "$egg"
    diff -u --label want --label actual "$out/$name.want" "$out/$name.actual" |
      sed 's/^/      /' | tail -n +3
    fail=$((fail + 1))
  fi
done

# Report how much work the random cases actually did: a case whose rules never fire has
# only its seeded terms, and tests little beyond action evaluation.
if compgen -G "$out/rand-*.want" >/dev/null; then
  echo "difftest: random-case total row counts:"
  for w in "$out"/rand-*.want; do awk '{s += $2} END {print s}' "$w"; done |
    sort -n | uniq -c | awk '{printf "    %3d rows: %d cases\n", $2, $1}'
  echo "difftest: $(for w in "$out"/rand-*.want; do tr '\n' ' ' <"$w"; echo; done |
    sort -u | wc -l) distinct profiles"
fi
echo "difftest: $pass passed, $fail failed, $skipped skipped (generation timed out)"
[[ $fail -eq 0 ]]
