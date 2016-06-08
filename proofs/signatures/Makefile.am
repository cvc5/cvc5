# These CORE_PLFs are combined to give a "master signature" against
# which proofs are checked internally when using --check-proofs.  To
# add support for more theories, just list them here in the same order
# you would to the LFSC proof-checker binary.
#
CORE_PLFS = sat.plf smt.plf th_base.plf th_arrays.plf th_bv.plf th_bv_bitblast.plf th_bv_rewrites.plf th_real.plf th_int.plf

noinst_LTLIBRARIES = libsignatures.la

dist_pkgdata_DATA = \
	$(CORE_PLFS)

libsignatures_la_SOURCES = \
	signatures.cpp

BUILT_SOURCES = \
	signatures.cpp

signatures.cpp: $(CORE_PLFS)
	$(AM_V_GEN)( \
	  echo "namespace CVC4 {"; \
	  echo "namespace proof {"; \
	  echo; \
	  echo "extern const char *const plf_signatures;"; \
	  echo "const char *const plf_signatures = \"\\"; \
	  cat $+ | sed 's,\\,\\\\,g;s,",\\",g;s,$$,\\n\\,g'; \
	  echo "\";"; \
	  echo; \
	  echo "} /* CVC4::proof namespace */"; \
	  echo "} /* CVC4 namespace */"; \
	) > $@

EXTRA_DIST = \
	example.plf \
	example-arrays.plf \
	example-quant.plf \
	ex-mem.plf \
	th_quant.plf
