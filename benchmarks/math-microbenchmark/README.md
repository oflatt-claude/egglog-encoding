# Fixed Math Engine Comparison

This directory contains the one Math workload that can run through both
current egg and current egglog.

The language, 24 rewrites, and seven seed expressions come from the PLDI 2023
artifact for *Better Together: Unifying Datalog and Equality Saturation*:

- DOI: <https://doi.org/10.5281/zenodo.7709794>
- Archive SHA-256: `2f061f4f59fd3404638db0d9ad9d130e008d4c41fdeb58ade30684d8e424607a`
- egg source: `micro-benchmarks/src/math.rs`
- Eqlog source: `micro-benchmarks/src/eqlog/math_full.egg`

`math.egg` is the self-contained current-egglog port and preserves the
artifact's Rational constants. The `egg-math-benchmark` workspace crate
directly ports the egg language and rewrites to egg 0.11.0.

`math.egg` contains eleven explicit `(run)` leaves inside one schedule.
It deliberately uses the ordinary simple/seminaive schedulers, without the
artifact's backoff scheduler or match cap. The fixture therefore supports a
controlled current-engine comparison; it is not an exact reproduction of the
paper's historical scheduler results.

The final equality is:

```lisp
(= (+ (cos x) (cos x))
   (d x (+ (sin x) (sin x))))
```

Both engines first establish this equality on iteration eleven: the corresponding
tests require failure after ten iterations and success after eleven. This makes
the terminal check an execution-depth guard rather than a seed or first-step
identity.

The `bench.py` egg treatments are supported only for this fixture. For example:

```bash
# egg proof overhead
./bench.py benchmarks/math-microbenchmark/math.egg \
  --compare-treatment egg --treatment egg-proofs

# current egglog versus current egg, both without proof recording
./bench.py benchmarks/math-microbenchmark/math.egg \
  --compare-treatment egg --treatment off
```

Every treatment runs the same fixed workload command. The four egg modes are
plain execution, explanation recording, explanation extraction, and
explanation checking. The five egglog modes are off, term encoding, proof
recording, proof extraction, and proof testing.
