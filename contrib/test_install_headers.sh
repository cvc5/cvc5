#!/bin/bash
# contrib/test_install_headers.sh
# Tim King <taking@google.com> for the CVC4 project, 24 December 2015
#
# ./contrib/test_install_headers.sh <INSTALL>
#
# This files tests the completeness of the public headers for CVC4.
# Any header marked by #include "cvc4_public.h" in either the builds/
# or src/ directory is installed into the path INSTALL/include/cvc4 where
# INSTALL is set using the --prefix=INSTALL flag at configure time.
# This test uses find to attempt to include all of the headers in
# INSTALL/include/cvc4 and compiles a simple cpp file.

INSTALLATION=$1
CXX=g++
LDFLAGS=-lcln
CXXFILE=test_cvc4_header_install.cpp
OUTFILE=test_cvc4_header_install

echo $INSTALLATION

echo "Generating $CXXFILE"
find $INSTALLATION/include/cvc4/ -name *.h -printf '%P\n' | \
		 awk '{ print "#include <cvc4/" $0 ">"}' > $CXXFILE
echo "int main() { return 0; }" >> $CXXFILE

echo "Compiling $CXXFILE into $OUTFILE"
echo "$CXX -I$INSTALLATION/include -L$INSTALLATION/lib $LDFLAGS -o $OUTFILE $CXXFILE"
$CXX -I$INSTALLATION/include -L$INSTALLATION/lib $LDFLAGS -o $OUTFILE $CXXFILE

read -p "Do you want to delete $CXXFILE and $OUTFILE? [y/n]" yn
case $yn in
		[Nn]* ) exit;;
		[Yy]* ) rm "$OUTFILE" "$CXXFILE";;
		* ) echo "Did not get a yes or no answer. Exiting."; exit;;
esac
