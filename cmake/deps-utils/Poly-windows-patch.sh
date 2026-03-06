#!/bin/sh
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################

# Roughly following https://stackoverflow.com/a/44383330/2375725
# Avoid %z and %llu format specifiers
find $1/ -type f ! -name "*.orig" -exec \
     sed -i.orig "s/%z[diu]/%\\\" PRIu64 \\\"/g" {} +
find $1/ -type f ! -name "*.orig" -exec \
     sed -i.orig "s/%ll[du]/%\\\" PRIu64 \\\"/g" {} +

# Make sure the new macros are available
find $1/ -type f ! -name "*.orig" -exec \
     sed -i.orig "s/#include <stdio.h>/#include <stdio.h>\\n#include <inttypes.h>/" {} +
find $1/ -type f ! -name "*.orig" -exec \
     sed -i.orig "s/#include <cstdio>/#include <cstdio>\\n#include <inttypes.h>/" {} +
