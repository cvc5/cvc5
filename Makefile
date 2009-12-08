.PHONY: _default_build_
_default_build_: all
%:
	@if test -e builds; then \
		echo cd builds; \
		cd builds; \
		echo $(MAKE) $@; \
		$(MAKE) $@; \
	else \
		echo; \
		echo 'Run configure first, or type "make" in a configured build directory.'; \
		echo; \
	fi

distclean:
	@if test -e builds; then \
		echo cd builds; \
		cd builds; \
		echo $(MAKE) $@; \
		$(MAKE) $@; \
	fi
	rm -rf builds
