#!/bin/bash
#
# Patch to cudd build system to build everything with libtool, supporting
# shared libraries.  Also all libraries are combined into a single one.
#
# This script applies the patch, builds cudd, and, assuming there are no
# errors, reverses the patch.
#
# -- Morgan Deters <mdeters@cs.nyu.edu>  Wed, 13 Jul 2011 18:03:11 -0400
#

cd "$(dirname "$0")"
if [ $# -ne 1 -o "$1" = -h -o "$1" = -help -o "$1" = --help ]; then
  echo "usage: $(basename "$0") cudd-dir" >&2
  exit 1
fi

patch="$(pwd)/$(basename "$0")"
if [ ! -r "$patch" ]; then
  echo "error: can't read patch at \`$patch'" >&2
  exit 1
fi
if ! expr "$1" : / &>/dev/null; then
  echo "error: must specify an absolute path to cudd sources" >&2
  exit 1
fi
cudd_dir="$1"

arch=$(../config/config.guess | cut -f1 -d-)
case "$arch" in
  i?86)   XCFLAGS='-mtune=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD' ;;
  x86_64) XCFLAGS='-mtune=native -DHAVE_IEEE_754 -DBSD -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8' ;;
  *)      XCFLAGS= ;;
esac

set -ex

XCFLAGS="$XCFLAGS"

version_info=0:0:0

prefix="$cudd_dir"
eprefix="$prefix"
bindir="$eprefix/bin"
datadir="$prefix/share"
includedir="$prefix/include"
libdir="$prefix/lib"
mandir="$datadir/man/man1"
docdir="$datadir/doc"

cd "$cudd_dir"
patch -p1 < "$patch"
make "XCFLAGS=$XCFLAGS" "CC=libtool --mode=compile gcc" "CPP=libtool --mode=compile g++" libdir="$libdir" version_info="$version_info" DDDEBUG= MTRDEBUG= ICFLAGS=-O2
mkdir -p "$libdir"
libtool --mode=install cp libcudd.la "$libdir/libcudd.la"
libtool --mode=install cp libcuddxx.la "$libdir/libcuddxx.la"
libtool --mode=install cp libdddmp.la "$libdir/libdddmp.la"
libtool --finish "$libdir"
patch -p1 -R < "$patch"
exit

# patch follows

--- a/Makefile
+++ b/Makefile
@@ -221,11 +221,16 @@
 
 build:
 	sh ./setup.sh
-	@for dir in $(DIRS); do \
+	+@for dir in $(BDIRS) obj; do \
 		(cd $$dir; \
 		echo Making $$dir ...; \
-		make CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )\
+		make CC="$(CC)" RANLIB="$(RANLIB)" MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )\
 	done
+	libtool --mode=link gcc -rpath "$(libdir)" -version-info "$(version_info)" -o libcudd.la cudd/libcudd.la mtr/libmtr.la epd/libepd.la util/libutil.la st/libst.la -lm
+	libtool --mode=link gcc -rpath "${libdir}" -version-info "$(version_info)" -o libdddmp.la dddmp/libdddmp.la
+	libtool --mode=link g++ -rpath "$(libdir)" -version-info "$(version_info)" -o libcuddxx.la obj/libobj.la -lcudd
+	+@(cd nanotrav; \
+	make CC="$(CC)" RANLIB="$(RANLIB)" MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )
 
 nanotrav: build
 
@@ -319,4 +324,6 @@
 	     echo Cleaning $$dir ...; \
 	     make -s EXE="$(EXE)" distclean	) \
 	done
+	rm -f libcudd* libdddmp*
+	rm -fr .libs
 	sh ./shutdown.sh
--- a/cudd/Makefile
+++ b/cudd/Makefile
@@ -59,7 +59,7 @@
 	  cuddZddPort.c cuddZddReord.c cuddZddSetop.c cuddZddSymm.c \
 	  cuddZddUtil.c
 PHDR    = cudd.h cuddInt.h
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 TARGET	= test$(P)$(EXE)
 TARGETu = test$(P)-u
@@ -71,12 +71,11 @@
 
 #------------------------------------------------------
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PSRC) $(PHDR)
-	$(CC) -c  $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG) 
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)
 
 optimize_dec: lib$(P).b
 
@@ -116,9 +115,10 @@
 programs: $(TARGET) $(TARGETu) lintpgm
 
 clean:
-	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
+	rm -f *.o *.lo *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
 	.pure core *.warnings
 
 distclean: clean
-	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
+	rm -f $(TARGET) $(TARGETu) lib*.a lib*.la lib$(P).b llib-l$(P).ln \
 	*.bak *~ tags .gdb_history *.qv *.qx
+	rm -fr .libs
--- a/dddmp/Makefile
+++ b/dddmp/Makefile
@@ -148,7 +148,7 @@
 	  dddmpStoreMisc.c dddmpUtil.c dddmpBinary.c dddmpConvert.c \
           dddmpDbg.c 
 PHDR    = dddmp.h dddmpInt.h $(INCLUDE)/cudd.h $(INCLUDE)/cuddInt.h
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 TARGET	= test$(P)$(EXE)
 TARGETu = test$(P)-u
@@ -182,12 +182,11 @@
 	$(WHERE)/mtr/llib-lmtr.ln $(WHERE)/st/llib-lst.ln \
 	$(WHERE)/util/llib-lutil.ln
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PHDR)
-	$(CC) -c $< -I$(INCLUDE) $(ICFLAGS) $(XCFLAGS) $(DDDEBUG) $(MTRDEBUG) $(DDDMPDEBUG) $(LDFLAGS)
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(ICFLAGS) $(XCFLAGS) $(DDDEBUG) $(MTRDEBUG) $(DDDMPDEBUG) $(LDFLAGS)
 
 optimize_dec: lib$(P).b
 
@@ -231,12 +230,13 @@
 #----------------------------------------------------------------------------#
 
 clean:
-	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
+	rm -f *.o *.lo *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
 	.pure core *.warnings
 
 distclean: clean
-	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
+	rm -f $(TARGET) $(TARGETu) lib*.a lib*.la lib$(P).b llib-l$(P).ln \
 	*.bak *~ tags .gdb_history *.qv *.qx
+	rm -fr .libs
 
 
 
--- a/epd/Makefile
+++ b/epd/Makefile
@@ -19,7 +19,7 @@
 P	= epd
 PSRC	= epd.c
 PHDR	= epd.h
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 
 WHERE	= ..
@@ -27,12 +27,11 @@
 
 #---------------------------
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PSRC) $(PHDR)
-	$(CC) -c $< -I$(INCLUDE) $(CFLAGS)
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(CFLAGS)
 
 optimize_dec: lib$(P).b
 
@@ -58,7 +57,8 @@
 all: lib$(P).a lib$(P).b llib-l$(P).ln tags
 
 clean:
-	rm -f *.o *.u .pure *.warnings
+	rm -f *.o *.lo *.u .pure *.warnings
 
 distclean: clean
-	rm -f lib*.a lib$(P).b llib-l$(P).ln tags *~ *.bak *.qv *.qx
+	rm -f lib*.a lib*.la lib$(P).b llib-l$(P).ln tags *~ *.bak *.qv *.qx
+	rm -fr .libs
--- a/mtr/Makefile
+++ b/mtr/Makefile
@@ -30,7 +30,7 @@
 P	= mtr
 PSRC    = mtrBasic.c mtrGroup.c
 PHDR    = mtr.h
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 SRC	= test$(P).c
 HDR	=
@@ -49,12 +49,11 @@
 
 #---------------------------
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PSRC) $(PHDR)
-	$(CC) -c  $< -I$(INCLUDE) $(CFLAGS) $(MTRDEBUG) 
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(CFLAGS) $(MTRDEBUG)
 
 optimize_dec: lib$(P).b
 
@@ -88,9 +87,10 @@
 	cc -O3 $(XCFLAGS) $(LDFLAGS) -o $@ $(UBJ) $(BLIBS) -lm
 
 clean:
-	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
+	rm -f *.o *.lo *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
 	.pure core *.warnings
 
 distclean: clean
-	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
+	rm -f $(TARGET) $(TARGETu) lib*.a lib*.la lib$(P).b llib-l$(P).ln \
 	*.bak *~ tags *.qv *.qx
+	rm -fr .libs
--- a/nanotrav/Makefile
+++ b/nanotrav/Makefile
@@ -19,9 +19,7 @@
 
 INCLUDE = $(WHERE)/include
 
-LIBS	= $(WHERE)/dddmp/libdddmp.a $(WHERE)/cudd/libcudd.a \
-	$(WHERE)/mtr/libmtr.a $(WHERE)/st/libst.a $(WHERE)/util/libutil.a \
-	$(WHERE)/epd/libepd.a
+LIBS	= $(WHERE)/libcudd.la $(WHERE)/libdddmp.la
 
 MNEMLIB =
 #MNEMLIB	= $(WHERE)/mnemosyne/libmnem.a
@@ -39,7 +37,7 @@
 HDR	= bnet.h ntr.h $(WHERE)/include/dddmp.h $(WHERE)/include/cudd.h \
 	$(WHERE)/include/cuddInt.h
 
-OBJ	= $(SRC:.c=.o)
+OBJ	= $(SRC:.c=.lo)
 UBJ	= $(SRC:.c=.u)
 
 MFLAG	=
@@ -61,10 +59,10 @@
 #------------------------------------------------------
 
 $(TARGET): $(SRC) $(OBJ) $(HDR) $(LIBS) $(MNEMLIB)
-	$(PURE) $(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm
+	libtool --mode=link gcc $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm
 
-.c.o: $(HDR)
-	$(CC) -c $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)
 
 # if the header files change, recompile
 $(OBJ): $(HDR)
@@ -91,8 +89,9 @@
 	pixie $(TARGETu)
 
 clean:
-	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
+	rm -f *.o *.lo *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
 	.pure core *.warnings
 
 distclean: clean
 	rm -f $(TARGET) $(TARGETu) *.bak *~ .gdb_history *.qv *.qx
+	rm -fr .libs
--- a/obj/Makefile
+++ b/obj/Makefile
@@ -45,7 +45,7 @@
 P	= obj
 PSRC	= cuddObj.cc
 PHDR	= cuddObj.hh $(INCLUDE)/cudd.h
-POBJ	= $(PSRC:.cc=.o)
+POBJ	= $(PSRC:.cc=.lo)
 PUBJ	= $(PSRC:.cc=.u)
 TARGET	= test$(P)$(EXE)
 TARGETu = test$(P)-u
@@ -57,12 +57,11 @@
 
 #------------------------------------------------------
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link g++ -o $@ $?
 
-.cc.o: $(PHDR)
-	$(CPP) -c $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)
+%.lo: %.cc
+	$(CPP) -c -o $@ $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)
 
 optimize_dec: lib$(P).b
 
@@ -102,9 +101,10 @@
 programs: $(TARGET) $(TARGETu) lintpgm
 
 clean:
-	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
+	rm -f *.o *.lo *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
 	.pure core *.warnings
 
 distclean: clean
-	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
+	rm -f $(TARGET) $(TARGETu) lib*.a lib*.la lib$(P).b llib-l$(P).ln \
 	*.bak *~ tags .gdb_history *.qv *.qx
+	rm -fr .libs
--- a/st/Makefile
+++ b/st/Makefile
@@ -19,7 +19,7 @@
 P	= st
 PSRC	= st.c
 PHDR	= st.h
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 
 WHERE	= ..
@@ -27,12 +27,11 @@
 
 #---------------------------
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PHDR)
-	$(CC) -c $< -I$(INCLUDE) $(CFLAGS)
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(CFLAGS)
 
 optimize_dec: lib$(P).b
 
@@ -58,7 +57,8 @@
 all: lib$(P).a lib$(P).b llib-l$(P).ln tags
 
 clean:
-	rm -f *.o *.u .pure *.warnings
+	rm -f *.o *.lo *.u .pure *.warnings
 
 distclean: clean
-	rm -f lib*.a lib$(P).b llib-l$(P).ln tags *~ *.bak *.qv *.qx
+	rm -f lib*.a lib*.la lib$(P).b llib-l$(P).ln tags *~ *.bak *.qv *.qx
+	rm -fr .libs
--- a/util/Makefile
+++ b/util/Makefile
@@ -21,19 +21,18 @@
 PSRC	= cpu_time.c cpu_stats.c getopt.c safe_mem.c strsav.c texpand.c \
 	  ptime.c prtime.c pipefork.c pathsearch.c stub.c \
 	  tmpfile.c datalimit.c
-POBJ	= $(PSRC:.c=.o)
+POBJ	= $(PSRC:.c=.lo)
 PUBJ	= $(PSRC:.c=.u)
 PHDR	= util.h
 
 WHERE	= ..
 INCLUDE = $(WHERE)/include
 
-lib$(P).a: $(POBJ)
-	ar rv $@ $?
-	$(RANLIB) $@
+lib$(P).la: $(POBJ)
+	libtool --mode=link gcc -o $@ $?
 
-.c.o: $(PHDR)
-	$(CC) -c $< -I$(INCLUDE) $(FLAGS) $(CFLAGS)
+%.lo: %.c
+	$(CC) -c -o $@ $< -I$(INCLUDE) $(FLAGS) $(CFLAGS)
 
 optimize_dec: lib$(P).b
 
@@ -59,7 +58,8 @@
 all: lib$(P).a lib$(P).b llib-l$(P).ln tags
 
 clean:
-	rm -f *.o *.u core *.warnings
+	rm -f *.o *.lo *.u core *.warnings
 
 distclean: clean
-	rm -f lib$(P).a lib$(P).b llib-l$(P).ln tags *.bak *~ .pure
+	rm -f lib$(P).a lib$(P).la lib$(P).b llib-l$(P).ln tags *.bak *~ .pure
+	rm -fr .libs
