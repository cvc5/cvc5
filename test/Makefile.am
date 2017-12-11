SUBDIRS = unit system regress .

MAKEFLAGS = -k

.PHONY: units systemtests regress regress0 regress1 regress2 regress3 regress4
units systemtests regress regress0 regress1 regress2 regress3 regress4:
	@$(MAKE) check-pre; \
	for dir in $(SUBDIRS); do \
		test $$dir = . || (cd $$dir && $(MAKE) $(AM_MAKEFLAGS) $@); \
	done; \
	$(MAKE) check-local

# synonyms for "check" in this directory
.PHONY: test
test: check

am__tty_colors = \
red=; grn=; lgn=; blu=; mag=; std=; \
test "X$(AM_COLOR_TESTS)" != Xno \
&& test "X$$TERM" != Xdumb \
&& { test "X$(AM_COLOR_TESTS)" = Xalways || test -t 1 2>/dev/null; } \
&& { \
  red='[0;31m'; \
  grn='[0;32m'; \
  lgn='[1;32m'; \
  blu='[1;34m'; \
  mag='[1;35m'; \
  std='[m'; \
}

subdirs_to_check = \
	regress/regress0 \
	regress/regress0/arith \
	regress/regress0/arith/integers \
	regress/regress0/arrays \
	regress/regress0/aufbv \
	regress/regress0/auflia \
	regress/regress0/bv \
	regress/regress0/bv/core \
	regress/regress0/datatypes \
	regress/regress0/decision \
	regress/regress0/expect \
	regress/regress0/fmf \
	regress/regress0/ho \
	regress/regress0/lemmas \
	regress/regress0/nl \
	regress/regress0/parser \
	regress/regress0/precedence \
	regress/regress0/preprocess \
	regress/regress0/push-pop \
	regress/regress0/push-pop/arith \
	regress/regress0/push-pop/boolean \
	regress/regress0/quantifiers \
	regress/regress0/rels \
	regress/regress0/rewriterules \
	regress/regress0/sep \
	regress/regress0/sets \
	regress/regress0/strings \
	regress/regress0/sygus \
	regress/regress0/tptp \
	regress/regress0/uf \
	regress/regress0/uflia \
	regress/regress0/uflra \
	regress/regress0/unconstrained \
	regress/regress1 \
	regress/regress1/aufbv \
	regress/regress1/auflia \
	regress/regress1/bv \
	regress/regress1/datatypes \
	regress/regress1/decision \
	regress/regress1/fmf \
	regress/regress1/lemmas \
	regress/regress1/rewriterules \
	regress/regress1/sep \
	regress/regress1/sets \
	regress/regress1/strings \
	regress/regress1/sygus \
	regress/regress1/quantifiers \
	regress/regress2 \
	regress/regress2/arith \
	regress/regress3 \
	regress/regress4 \
	system \
	unit

check-recursive: check-pre
.PHONY: check-pre
check-pre:
	@rm -f $(subdirs_to_check:=/test-suite.log)

if HAVE_CXXTESTGEN
HANDLE_UNIT_TEST_SUMMARY = \
	if test -s "unit/test-suite.log"; then :; else \
		echo "$${red}Unit tests did not run; maybe there were compilation problems ?$$std"; \
	fi
else
HANDLE_UNIT_TEST_SUMMARY = \
	echo "$${mag}Unit tests not supported, since CxxTest wasn't found$$std"; \
	rm -f "unit/test-suite.log"
endif

if AUTOMAKE_1_11
# automake 1.11 version
check-local:
	@$(am__tty_colors); \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std; \
	$(HANDLE_UNIT_TEST_SUMMARY); \
	if test -s "system/test-suite.log"; then :; else \
		echo "$${red}System tests did not run; maybe there were compilation problems ?$$std"; \
	fi; \
	for dir in $(subdirs_to_check); do \
		log=$$dir/test-suite.log; \
		if test -s "$$log"; then \
			status="`head -n 5 $$log | tail -1`"; \
			if echo "$$status" | grep -q failed; then \
				echo "$$red$$status"; \
				echo "    @abs_builddir@/$$log$$std"; \
			else \
				printf "$$grn%-30s in $$dir$$std\\n" "$$status"; \
			fi; \
		fi; \
	done; \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std
else
# automake 1.12 version
check-local:
	@$(am__tty_colors); \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std; \
	$(HANDLE_UNIT_TEST_SUMMARY); \
	if test -s "system/test-suite.log"; then :; else \
		echo "$${red}System tests did not run; maybe there were compilation problems ?$$std"; \
	fi; \
	for dir in $(subdirs_to_check); do \
		log=$$dir/test-suite.log; \
		if test -s "$$log"; then \
			status="`head -n 11 $$log | tail -7`"; \
			nicestatus="`echo $$status | sed 's/# [A-Z]*: 0 *//g;s/# \([A-Z]*\): \([0-9]*\)/\2 \1,/g;s/, *$$//;'`"; \
			if	echo "$$status" | grep -q '# FAIL:  0' && \
				echo "$$status" | grep -q '# XPASS: 0' && \
				echo "$$status" | grep -q '# ERROR: 0' && \
				echo "$$status" | grep -q '# SKIP:  0'; then \
				printf "$$grn%-30s in $$dir$$std\\n" "$$nicestatus"; \
			else \
				echo "$$red$$nicestatus"; \
				echo "    @abs_builddir@/$$log$$std"; \
			fi; \
		fi; \
	done; \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std
endif
