# Semantics/proof development is independent of paper experiment validation.
TARGETS := lean-check lean-difftest lean-compiled-difftest lean-congruence-test lean-provenance-test lean-resugar-test lean-certificate-test lean-update-fixtures lean-egg-test lean-update-egg-snapshots paper paper-check paper-extract
.PHONY: $(TARGETS)
.DEFAULT_GOAL := lean-check
export RUST_TEST_ARGS LEAN_BIN_DIR LEAN_CERTIFICATES
$(TARGETS):
	python3 check.py $@
