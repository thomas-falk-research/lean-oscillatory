# Every target exits non-zero on failure. A target with nothing to check yet writes build/skipped/<target>;
# verify-all then reports INCOMPLETE, never PASS.
LAKE ?= lake
T := tools/target/release
B := build
SKIP = mkdir -p $(B)/skipped && touch $(B)/skipped/$@
UNSKIP = mkdir -p $(B)/skipped && rm -f $(B)/skipped/$@
LATEST_STAMP = $(lastword $(sort $(wildcard stamps/2*/)))

.PHONY: tools tools-test verify-toolchain lean guard lean-replay commit comparator stamp stamp-verify verify-all numerics

tools:
	cd tools && cargo build --release --locked --quiet

tools-test:
	cd tools && cargo test --release --locked --quiet

verify-toolchain: tools
	$(T)/toolchain .

guard: tools
	$(T)/guard .

lean: tools
	$(LAKE) build
	mkdir -p $(B) && $(LAKE) env lean Axioms.lean > $(B)/axioms.out
	$(T)/audit $(B)/axioms.out . $(B)/audited.txt
	$(LAKE) env lean StatementTypes.lean
	$(LAKE) env lean MathlibNames.lean > /dev/null

lean-replay: lean
	$(T)/replay . $(B)/audited.txt $(B)/replay

commit: lean
	$(UNSKIP); $(LAKE) build oscint-commit-env && { $(T)/commit $(B)/commit || { [ $$? -eq 3 ] && $(SKIP); }; }

comparator:
	$(UNSKIP); if [ -f comparator.json ]; then $(T)/challenge . $(LATEST_STAMP); else echo "comparator: SKIPPED: no frozen challenge yet"; $(SKIP); fi

stamp: tools
	$(T)/stamp create . stamps/$(shell date -u +%Y%m%dT%H%M%SZ)-$(shell git rev-parse --short=12 HEAD)

stamp-verify: tools
	$(UNSKIP); if [ -n "$(LATEST_STAMP)" ]; then $(T)/stamp verify . $(LATEST_STAMP); else echo "stamp-verify: SKIPPED: no stamp yet"; $(SKIP); fi

verify-all: tools
	$(T)/verify_all

numerics:
	cd numerics && cargo build --release --locked --quiet && ./target/release/oscint-numerics
