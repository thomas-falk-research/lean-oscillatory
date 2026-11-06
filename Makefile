# Every target exits non-zero on failure. A target with nothing to check yet writes build/skipped/<target>;
# verify-all then reports INCOMPLETE, never PASS.
LAKE ?= lake
T := tools/target/release
B := build
SKIP = mkdir -p $(B)/skipped && touch $(B)/skipped/$@
UNSKIP = mkdir -p $(B)/skipped && rm -f $(B)/skipped/$@
LATEST_STAMP = $(lastword $(sort $(wildcard stamps/2*/)))

.PHONY: challenge-export tools tools-test verify-toolchain lean guard lean-replay commit comparator stamp stamp-verify verify-all numerics

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
	$(UNSKIP); if [ -f stamps/pins.txt ]; then $(T)/stamp verify-pinned .; else echo "stamp-verify: SKIPPED: no pinned stamp yet"; $(SKIP); fi

verify-all: tools
	$(T)/verify_all

numerics:
	cd numerics && cargo build --release --locked --quiet && ./target/release/oscint-numerics
