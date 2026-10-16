.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests slotted-check slotted-campaign slotted-eval slotted-check-no-oracle benchmark-smoke nightly nightly-local nightly-uv nightly-rustup \
	update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-doc-links rust-test

BENCHMARK_SMOKE_REPORT ?= /tmp/egglog-encoding-bench-smoke.jsonl

# No Ubuntu release packages uv, so `make nightly` installs a pinned copy into
# the checkout when uv is missing from PATH. uv then downloads its own CPython,
# so the runner needs neither uv nor Python 3.12.
UV_VERSION ?= 0.11.30
UV_BOOTSTRAP_DIR ?= $(CURDIR)/.uv/$(UV_VERSION)
NIGHTLY_UV = $(shell command -v uv || echo $(UV_BOOTSTRAP_DIR)/uv)

# Ubuntu's cargo predates rust-toolchain.toml's pin, so the nightly needs
# rustup's shims; scripts/nightly_bench.py puts them first on PATH.
CARGO_HOME_DIR ?= $(HOME)/.cargo

# Full validation is hygiene followed by tests.
check: nits test

# Nits are intentionally test-free.
nits: python-nits rust-nits

test: python-test rust-test

python-check: python-nits python-test

python-nits: python-lock python-format-check python-lint python-typecheck

python-lock:
	uv lock --check

python-format-check:
	uv run --locked ruff format --check .

python-lint:
	uv run --locked ruff check .

python-typecheck:
	uv run --locked mypy .

python-test:
	uv run --locked pytest -q

rust-check: rust-nits rust-test

rust-nits: rust-format-check rust-clippy rust-doc-links

rust-format-check:
	cargo fmt --all -- --check

rust-test:
	cargo test --workspace

rust-clippy:
	cargo clippy --workspace --all-targets -- -D warnings

# Clippy does not resolve doc links, and plain `cargo doc` skips the private
# items most of this codebase documents, so a rename leaves stale links behind
# unless rustdoc is run over them too.
rust-doc-links:
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items --workspace

# This is a name-filtered subset of rust-test, useful for proof iteration.
proof-tests:
	cargo test --workspace --test files 'proofs/'

# Slotted fixtures, compiler snapshots, reference comparisons, and mutation tests.
# The Python runner's --quick flag skips fuzzing; --no-oracle skips reference checks.
slotted-check:
	cargo build
	cargo test -p egglog-experimental --test slotted_snapshots
	cargo build --manifest-path slotted/xmulti/Cargo.toml
	cargo test --manifest-path slotted/xmulti/Cargo.toml
	python3 slotted/checks/check-slotted.py

# Larger randomized campaigns for graph equivalence, rule order, and checker mutations.
slotted-campaign:
	cargo build --release -p egglog-experimental
	cargo build --manifest-path slotted/xmulti/Cargo.toml
	python3 slotted/xdiff/campaign.py iso --cases 500 --seeds 32
	python3 slotted/xdiff/campaign.py order --cases 100 --seeds 32
	python3 slotted/xdiff/campaign.py checker --cases 200 --seeds 8
	XDIFF_DEPTH=3 XDIFF_DUP=0.4 XDIFF_SHARE=0.7 XDIFF_LAM=0.55 XDIFF_USEBIND=0.6 \
		python3 slotted/xdiff/campaign.py iso --cases 300 --seeds 8

# The paper's case studies -- the S4.1 array goal and the S4.2 SDQL workloads -- on the
# encoding and on the reference through both of its matchers, at the artifact's budgets.
# Release builds of both binaries, since these are the numbers a graph is drawn from.
slotted-eval:
	./bench.py slotted --params 0 1 2 3 --counts

slotted-check-no-oracle:
	cargo build
	cargo test -p egglog-experimental --test slotted_snapshots
	python3 slotted/checks/check-slotted.py --no-oracle

# Smoke the runner on small files, not the full local benchmark suite.
benchmark-smoke:
	rm -f -- "$(BENCHMARK_SMOKE_REPORT)"
	uv run --locked ./bench.py \
		egglog-experimental/tests/math-microbenchmark-rational.egg \
		egglog-experimental/tests/disequality/congruence.egg --rounds 1 \
		--report "$(BENCHMARK_SMOKE_REPORT)" --format markdown > /dev/null
	uv run --locked python -c \
		'from pathlib import Path; import sys; from benchmarking.reports.store import ReportStore; assert ReportStore(Path(sys.argv[1])).row_count > 0' \
		"$(BENCHMARK_SMOKE_REPORT)"

# Publish nightly/output/ for the egraphs-good nightly service
# (nightly.cs.washington.edu), which runs this target and serves that directory.
nightly: nightly-uv nightly-rustup
	CARGO_HOME="$(CARGO_HOME_DIR)" $(NIGHTLY_UV) run --locked python scripts/nightly_bench.py

nightly-uv:
	@command -v uv >/dev/null || test -x "$(UV_BOOTSTRAP_DIR)/uv" || \
		curl -LsSf https://astral.sh/uv/$(UV_VERSION)/install.sh \
			| env UV_INSTALL_DIR="$(UV_BOOTSTRAP_DIR)" UV_NO_MODIFY_PATH=1 sh

nightly-rustup:
	@test -x "$(CARGO_HOME_DIR)/bin/rustup" || \
		curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
			| env CARGO_HOME="$(CARGO_HOME_DIR)" sh -s -- \
				-y --no-modify-path --default-toolchain none

# The nightly host's run at one round, for trying it locally. nightly/output/ is
# git-ignored, so this writes it just as the host does.
nightly-local: nightly-uv nightly-rustup
	CARGO_HOME="$(CARGO_HOME_DIR)" $(NIGHTLY_UV) run --locked python scripts/nightly_bench.py --rounds 1

update-snapshots:
	uv run --locked pytest -q --snapshot-update --snapshot-details
	INSTA_UPDATE=always cargo test -p egglog-experimental --test slotted_snapshots

format:
	uv run --locked ruff format .
	cargo fmt --all
