.PHONY: default
default:
	@if test -e builds; then \
		echo cd builds; \
		cd builds; \
		echo $(MAKE); \
		$(MAKE); \
	else \
		echo; \
		echo 'Run configure first, or type "make" in a configured build directory.'; \
		echo; \
	fi
