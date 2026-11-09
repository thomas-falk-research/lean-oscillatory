# SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
#
# SPDX-License-Identifier: Apache-2.0

# Every target exits non-zero on failure. A target with nothing to check yet writes build/skipped/<target>;
# verify-all then reports INCOMPLETE, never PASS.
LAKE ?= lake
T := tools/target/release
B := build
SKIP = mkdir -p $(B)/skipped && touch $(B)/skipped/$@
UNSKIP = mkdir -p $(B)/skipped && rm -f $(B)/skipped/$@
LATEST_STAMP = $(lastword $(sort $(wildcard stamps/2*/)))

.PHONY: api api-check challenge-export tools tools-test verify-toolchain lean guard lean-replay commit comparator stamp stamp-verify verify-all numerics \
	quick statements statements-check release-pin entry-point

tools:
	cd tools && cargo build --release --locked --quiet

tools-test:
	cd tools && cargo test --release --locked --quiet

verify-toolchain: tools
	$(T)/toolchain .

guard: tools
	$(T)/guard .

# `lean` runs once per change: `lean-replay`, `commit` and `comparator` depend on the marker `$(B)/lean.ok`, which
# is rebuilt only when a Lean source, the Lake configuration or the toolchain pin is newer (lessons 7).
LEAN_INPUTS := $(shell find OscInt Blueprint Challenge tools/lean -name '*.lean' 2>/dev/null) OscInt.lean Blueprint.lean \
	Challenge.lean Axioms.lean StatementTypes.lean MathlibNames.lean GammaFree.lean lakefile.toml lake-manifest.json \
	lean-toolchain

$(B)/lean.ok: $(LEAN_INPUTS)
	$(MAKE) lean

lean: tools
	rm -f $(B)/lean.ok
	$(LAKE) build
	mkdir -p $(B) && $(LAKE) env lean Axioms.lean > $(B)/axioms.out
	$(T)/audit $(B)/axioms.out . $(B)/audited.txt
	$(LAKE) env lean StatementTypes.lean
	$(LAKE) env lean MathlibNames.lean > /dev/null
	$(LAKE) env lean GammaFree.lean
	touch $(B)/lean.ok

lean-replay: $(B)/lean.ok tools
	$(T)/replay . $(B)/audited.txt $(B)/replay

commit: $(B)/lean.ok tools
	$(UNSKIP); $(LAKE) build oscint-commit-env && { $(T)/commit $(B)/commit || { [ $$? -eq 3 ] && $(SKIP); }; }

comparator: $(B)/lean.ok tools
	$(UNSKIP); $(T)/challenge check-all . || { [ $$? -eq 3 ] && $(SKIP); }

challenge-export: tools
	$(T)/challenge export-all .

stamp: commit challenge-export
	$(T)/stamp create . stamps/$(shell date -u +%Y%m%dT%H%M%SZ)-$(shell git rev-parse --short=12 HEAD)

stamp-verify: tools
	$(UNSKIP); if [ -f stamps/pins.txt ]; then $(T)/stamp verify-every .; else echo "stamp-verify: SKIPPED: no pinned stamp yet"; $(SKIP); fi

# `make verify-all ONLY="lean guard"` runs only those steps (reported as a partial run, never as a full PASS).
verify-all: tools
	$(T)/verify_all $(foreach s,$(ONLY),--only $(s))

# The fast local loop and the pull-request CI job: build, guard, axiom audit, statement types, Mathlib names,
# Gamma-free check, statement list. Minutes with a warm cache; `verify-all` adds the kernel replay, commitments,
# comparator and stamps (about an hour).
quick: guard statements-check api-check
	$(MAKE) --no-print-directory lean
	$(MAKE) --no-print-directory entry-point

# `import OscInt.API` exposes every statement and proving theorem of stamps/statements.json, and the P1 acceptance
# example (front ends on phases given only by a formula) elaborates against the root build.
entry-point:
	tools/check_entry_point.sh --self-test && tools/check_entry_point.sh
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerFormula.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerLocal.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerLocalChecks.lean
	$(LAKE) env lean -DautoImplicit=false examples/api/Snippets.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerLattice.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerGlobalChecks.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerLatticeExplicit.lean
	$(LAKE) env lean -DautoImplicit=false examples/consumer/ConsumerVector.lean

# The API index docs/api.json and examples/api/Snippets.lean, generated from stamps/statements.json and
# docs/api/annotations.json (`tools/gen_api.py`); `api-check` fails on drift (and is part of `quick`).
api:
	python3 -I tools/gen_api.py .

api-check:
	tools/test_gen_api.sh && python3 -I tools/gen_api.py --check .

# stamps/statements.json: the machine-readable list of pinned statements for downstream projects (README).
statements: tools
	$(T)/statements gen .

statements-check: tools
	$(UNSKIP); $(T)/statements check . || { [ $$? -eq 3 ] && $(SKIP); }

numerics:
	cd numerics && cargo build --release --locked --quiet && ./target/release/oscint-numerics

# The release tag that README pins exists and its release notes give the pinned SHA-256s (tools/check_release_pin.sh).
release-pin:
	tools/check_release_pin.sh --self-test && tools/check_release_pin.sh
