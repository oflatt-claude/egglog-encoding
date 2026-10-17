# Validation recipes live in scripts/check.py; these names remain public aliases.
CHECK_TARGETS := \
	check nits test python-check python-nits rust-check rust-nits proof-tests \
	lean-check lean-difftest lean-congruence-test lean-provenance-test lean-resugar-test \
	lean-certificate-test lean-update-fixtures lean-egg-test lean-update-egg-snapshots \
	paper paper-check paper-extract update-snapshots format \
	python-lock python-format-check python-lint python-typecheck python-test \
	rust-format-check rust-clippy rust-doc-links rust-test
.PHONY: $(CHECK_TARGETS) benchmark-smoke nightly nightly-local nightly-uv nightly-rustup
.DEFAULT_GOAL := check

# Make command-line overrides reach the script without shell interpolation.
# RUST_TEST_ARGS is empty by default; constrained hosts can set --test-threads=1.
export RUST_TEST_ARGS LEAN_BIN_DIR LEAN_CERTIFICATES

$(CHECK_TARGETS):
	python3 scripts/check.py $@

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

# Use a disposable report path, keeping the default report cache untouched.
benchmark-smoke:
	rm -f -- "$(BENCHMARK_SMOKE_REPORT)"
	uv run --locked ./bench.py --rounds 1 \
		--report "$(BENCHMARK_SMOKE_REPORT)" --format markdown \
		egglog/tests/integer_math.egg > /dev/null
	uv run --locked python -c \
		'from pathlib import Path; import sys; from benchmarking.reports.store import ReportStore; assert ReportStore(Path(sys.argv[1])).row_count > 0' \
		"$(BENCHMARK_SMOKE_REPORT)"

# Benchmark each endpoint in nightly_bench.py's ENDPOINTS on this checkout and on
# main, then copy eval-live's interactive report to nightly/output/. The
# egraphs-good nightly service (nightly.cs.washington.edu) runs this target and
# serves that directory, matching `report=` in the nightly configuration.
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
