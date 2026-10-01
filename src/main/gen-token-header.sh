#!/bin/sh
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################

grep "\"[a-zA-Z][a-zA-Z0-9_-][a-zA-Z0-9_-]*\"" "$1" | \
  sed 's/.*'\"'\([a-zA-Z0-9_-]*\)'\"'.*/"\1",/' | \
  sort -u > "$2"
