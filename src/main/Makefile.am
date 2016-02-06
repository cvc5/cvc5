AM_CPPFLAGS = \
	-D__BUILDING_CVC4DRIVER \
	-I@builddir@/.. $(ANTLR_INCLUDES) -I@srcdir@/../include -I@srcdir@/..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas

bin_PROGRAMS = cvc4

noinst_LIBRARIES = libmain.a

libmain_a_SOURCES = \
	interactive_shell.h \
	interactive_shell.cpp \
	main.h \
	util.cpp

if CVC4_BUILD_PCVC4
bin_PROGRAMS += pcvc4
pcvc4_SOURCES = \
	main.cpp \
	portfolio.cpp \
	portfolio.h \
	portfolio_util.cpp \
	portfolio_util.h \
	command_executor.cpp \
	command_executor_portfolio.cpp \
	command_executor.h \
	command_executor_portfolio.h \
	driver_unified.cpp
pcvc4_LDADD = \
	libmain.a \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../libcvc4.la \
	$(READLINE_LIBS) \
	@builddir@/../lib/libreplacements.la

pcvc4_CPPFLAGS = $(AM_CPPFLAGS) $(BOOST_CPPFLAGS) -DPORTFOLIO_BUILD
pcvc4_LDADD += $(BOOST_THREAD_LIBS)
pcvc4_LDADD += $(BOOST_THREAD_LDFLAGS)

if STATIC_BINARY
pcvc4_LINK = $(CXXLINK) -all-static $(pcvc4_LDFLAGS)
else
pcvc4_LINK = $(CXXLINK) $(pcvc4_LDFLAGS)
endif
endif

cvc4_SOURCES = \
	main.cpp \
	command_executor.cpp \
	driver_unified.cpp
cvc4_LDADD = \
	libmain.a \
	@builddir@/../parser/libcvc4parser.la \
	@builddir@/../libcvc4.la \
	$(READLINE_LIBS) \
	@builddir@/../lib/libreplacements.la

BUILT_SOURCES = \
	$(TOKENS_FILES)

TOKENS_FILES = \
	cvc_tokens.h \
	smt1_tokens.h \
	smt2_tokens.h \
	tptp_tokens.h

cvc_tokens.h: @srcdir@/../parser/cvc/Cvc.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9_-][a-zA-Z0-9_-]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9_-]*\)'\''.*/"\1",/' | sort -u >$@
smt1_tokens.h: @srcdir@/../parser/smt1/Smt1.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9_-][a-zA-Z0-9_-]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9_-]*\)'\''.*/"\1",/' | sort -u >$@
smt2_tokens.h: @srcdir@/../parser/smt2/Smt2.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9_-][a-zA-Z0-9_-]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9_-]*\)'\''.*/"\1",/' | sort -u >$@
tptp_tokens.h: @srcdir@/../parser/tptp/Tptp.g
	$(AM_V_GEN)grep "'[a-zA-Z][a-zA-Z0-9_-][a-zA-Z0-9_-]*'" $^ | sed 's/.*'\''\([a-zA-Z0-9_-]*\)'\''.*/"\1",/' | sort -u >$@


clean-local:
	rm -f $(BUILT_SOURCES)

if STATIC_BINARY
cvc4_LINK = $(CXXLINK) -all-static $(cvc4_LDFLAGS)
else
cvc4_LINK = $(CXXLINK) $(cvc4_LDFLAGS)
endif

