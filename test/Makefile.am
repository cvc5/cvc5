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
	system \
	unit

check-recursive: check-pre
.PHONY: check-pre
check-pre:
	@rm -f $(subdirs_to_check:=/test-suite.log)
	@find regress -name '*.trs' -exec rm {} \;

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
	echo $${red}Upgrade to a newer version of Automake to get a more detailed summary; \
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
	for dir in `find regress -not -empty -type d`; do \
		status_info=`grep -d skip ":test-result: " $$dir/*`; \
		total=`echo "$$status_info" | grep ":test-result: " | wc -l`; \
		if [ $$total -ne 0 ]; then \
			status="$${std}$$total TOTAL"; \
			pass=`echo "$$status_info" | grep " PASS" | wc -l`; \
			if [ $$pass -ne 0 ]; then \
				status="$$status $${grn}$$pass PASS"; \
			fi; \
			fail=`echo "$$status_info" | grep " FAIL" | wc -l`; \
			if [ $$fail -ne 0 ]; then \
				status="$$status $${red}$$fail FAIL"; \
			fi; \
			xpass=`echo "$$status_info" | grep " XPASS" | wc -l`; \
			if [ $$xpass -ne 0 ]; then \
				status="$$status $${red}$$xpass XPASS"; \
			fi; \
			error=`echo "$$status_info" | grep " ERROR" | wc -l`; \
			if [ $$error -ne 0 ]; then \
				status="$$status $${red}$$error ERROR"; \
			fi; \
			skip=`echo "$$status_info" | grep " SKIP" | wc -l`; \
			if [ $$skip -ne 0 ]; then \
				status="$$status $${blu}$$skip SKIP"; \
			fi; \
			printf "$$grn%-30s in $$dir\\n" "$$status"; \
		fi; \
	done; \
	echo $${blu}===============================  TESTING SUMMARY  =============================$$std
endif
