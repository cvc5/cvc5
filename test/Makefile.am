SUBDIRS = unit system regress .

MAKEFLAGS = -k

.PHONY: units systemtests regress regress0 regress1 regress2 regress3
units systemtests regress regress0 regress1 regress2 regress3:
	@$(MAKE) check-pre; \
	for dir in $(SUBDIRS); do \
		test $$dir = . || (cd $$dir && $(MAKE) $(AM_MAKEFLAGS) $@); \
	done; \
	$(MAKE) check-local

# synonyms for "check" in this directory
.PHONY: test
test: check

am__tty_colors = \
red=; grn=; lgn=; blu=; std=; \
test "X$(AM_COLOR_TESTS)" != Xno \
&& test "X$$TERM" != Xdumb \
&& { test "X$(AM_COLOR_TESTS)" = Xalways || test -t 1 2>/dev/null; } \
&& { \
  red='[0;31m'; \
  grn='[0;32m'; \
  lgn='[1;32m'; \
  blu='[1;34m'; \
  std='[m'; \
}
subdirs_to_check = unit system regress/regress0 regress/regress0/arith regress/regress0/arith/integers regress/regress0/uf regress/regress0/bv regress/regress0/bv/core regress/regress0/arrays regress/regress0/datatypes regress/regress0/lemmas regress/regress0/push-pop regress/regress0/precedence regress/regress1 regress/regress2 regress/regress3
check-recursive: check-pre
.PHONY: check-pre
check-pre:
	@rm -f $(subdirs_to_check:=/test-suite.log)
check-local:
	@$(am__tty_colors); \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std; \
	if test -s "unit/test-suite.log"; then :; else \
		echo "$${red}Unit tests did not run; maybe there were compilation problems ?$$std"; \
        fi; \
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
