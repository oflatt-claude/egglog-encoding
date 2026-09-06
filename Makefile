.PHONY: \
	check nits test python-check python-nits rust-check rust-nits \
	proof-tests benchmark-smoke nightly nightly-local nightly-uv nightly-rustup \
	lean-check lean-difftest \
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

# elan installs here by default and is not on PATH in a non-login shell.
LEAN_BIN_DIR ?= $(HOME)/.elan/bin

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
	cargo test -p egglog-experimental --features dd-backend --test timing_summary_cli

rust-clippy:
	cargo clippy --workspace --all-targets -- -D warnings
	cargo clippy -p egglog-experimental --features dd-backend --all-targets -- -D warnings

# Clippy does not resolve doc links, and plain `cargo doc` skips the private
# items most of this codebase documents, so a rename leaves stale links behind
# unless rustdoc is run over them too.
rust-doc-links:
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --document-private-items --workspace

# This is a name-filtered subset of rust-test, useful for proof iteration.
proof-tests:
	cargo test --workspace --test files 'proofs/'

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

# The Lean formalization in semantics/. Kept out of `check` so the Rust and Python
# suites do not depend on a Lean toolchain; `elan` and a Mathlib cache are needed,
# see semantics/README.md. `lake build` only warns on a `sorry`, so the sources are
# grepped for one as well. The second grep drops backtick-quoted prose: two module
# docstrings discuss `sorry`, and without it the target can never pass.
# M11's correspondence statement is stated and not proved: `EgglogSemantics/Encoding/`
# carries exactly LEAN_OPEN_SORRIES of them, each with a vacuity witness beside it
# (`semantics/ENCODING.md`). None of them is a named obligation any more — both halves are
# now proved from properties of the state `execM` returned (`cong_sameClass_of_state`,
# `sameClass_cong_of_state`) — and the three that are left are three *mechanisms* rather than
# three clauses, because the clauses are now derived from one another. The action read-back is
# proved (`holdsBuild_of_execProgramM`, `viewRepr_self_of_execProgramM`) and so is the
# induction over `encode P`'s commands built on it (`UnionsInv`, `unionsInv_execM`), which
# closes `execM_unionsJoined` and supplies the totality `Database.ViewsCover` needs. The two
# clauses the factorisation used to run through are **refuted** and kept as records:
# `Database.ReadsSelf` and `Database.ViewsProduct`, by `ncTgt_not_readsSelf` and
# `ncTgt_not_viewsProduct` — a source rule fires once per member of a premise's congruence class
# while the encoded rule reads rows that sit at the union-find leader. Each is now stated at what
# its consumers spend instead: `Database.ViewsCover.shared` at one *shared* id tuple and
# `Database.UnionsJoined` at the endpoints' *ids*, both holding at the counterexample's own state
# (`ncTgt_shared_FB`, `ncTgt_unionsJoined`), as does `Database.UnionsRead` and the correspondence
# itself, which is why `correspond` still agrees on all 70 in-domain cases. And the coverage
# clause is now *derived*: the tuple it answers with is always the union-find leader's, so
# `Database.ViewsCover.of_viewLeaderRows` gets it from a row-transport clause plus totality, with
# `ncTgt_viewsCover` running that reduction at the very state the product form fails at. What is
# left: `unionsJoined_fire` is a target firing behind a source firing — the one command case the
# read-back does not reach, and it carries both of the induction's data clauses. It is the
# **forward** half's. The reading it fires on is now supplied rather than owed: `RowRepr` is the
# reading through live rows, `encStep_exists_rowRepr` turns the induction's `ViewRepr` into one
# at the pointwise `@UF` row root, and `encStep_rowMech` discharges the two row clauses
# `UnionsFire` takes — at the state the *next* encoded block runs at (`EncReached`, `EncStep`),
# which is where `execM_rebuildClosed` could not be asked. The forward half of
# `Encoding/Match.lean` is now written too: `mem_matchQuery_encodeQuery` turns a source reading
# of a query into a substitution the *emitted* query matches at, over `encodeQuery`'s flattening
# (`RowRead`, an id per subterm position through live rows) and its fresh-variable supply
# (`FreshEnv` plus `freshVar_inj` and the `@` prefix), with `ncTgt_mirror` running it at the
# instance. What is still open is the *reading* it consumes: `UnionsFire`'s clauses choose an id
# per source term rather than a function of it, say nothing that makes two **congruent** source
# terms read to one id — which is what the emitted `.eq` atom compares, since an encoded target
# asserts nothing — and cover a source term rather than a pattern instance. All three hold at
# the state an encoded block runs at and none is among the hypotheses, so what is wanted next is
# a further derived clause in `RowMech`'s shape. The run-wide index argument it used to sit
# beside is closed:
# `execM_rebuildClosed` is `Database.ViewJoined` per mechanism (the e-class rule, the column
# rules, the `@UF` edge a collision writes), proved outright — its four `Signature.IsCtor`
# carries off `encodePrelude`'s own proof vocabulary (`encodeSig_isCtor_symName` and
# companions) and its literal clause off the completeness half (`execM_ufLitsIsolated`).
#
# **The completeness half is closed.** `execM_soundTerms` is proved and so is
# `encode_corresponds_complete`, the half `encode_corresponds` states over the source's own
# e-nodes. It took one further domain clause, `EncodeDomain.headsScoped`: `encodeBuild` emits no
# action at all for a leaf, so a rule head that builds a bare variable the query does not bind
# stops the source block there while the encoded block runs on and asserts an equation the source
# never derives (`bare_build_invents_equality`, at a program every other clause admits). The
# clause is faithfulness, not a narrowing — egglog raises `TypeError::Unbound` for exactly this
# in `to_core_actions` (`egglog/src/core.rs:663-670`) — and the census is unmoved at 70 of 166.
# Everything else the half needed — the per-command induction, the merge phase, the firing fold,
# the maintenance families, the head obligation `encodedHeadSound` — was already proved. The
# rule-head match correspondence of `Encoding/Match.lean` is proved outright, encoder read-back
# included, and so is the rule-head build case it feeds (`entrySound_headBuild`). Everywhere
# outside `Encoding/` a `sorry` is a regression, and a new one inside it changes the count.
LEAN_OPEN_SORRIES = 1
LEAN_OPEN_SORRY_DIR = semantics/EgglogSemantics/Encoding

lean-check:
	cd semantics && PATH="$(LEAN_BIN_DIR):$$PATH" lake build
	! grep -rnw --include='*.lean' sorry semantics/EgglogSemantics | grep -v '`sorry`' | \
		grep -v '^$(LEAN_OPEN_SORRY_DIR)/'
	test "$$(grep -rnw --include='*.lean' sorry $(LEAN_OPEN_SORRY_DIR) | \
		grep -cv '`sorry`')" -eq $(LEAN_OPEN_SORRIES)

# Differentially test the Lean semantics against egglog: for each generated program, the
# Lean interpreter's per-constructor row counts against egglog's `(print-size)`. Needs a
# release egglog binary (`cargo build --release -p egglog`) or EGGLOG_BIN.
lean-difftest:
	./scripts/difftest.sh

update-snapshots:
	uv run --locked pytest -q --snapshot-update --snapshot-details

format:
	uv run --locked ruff format .
	cargo fmt --all
