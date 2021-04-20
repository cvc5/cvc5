###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(LIBCONTEXT_SOURCES
  backtrackable.h
  cddense_set.h
  cdhashmap.h
  cdhashmap_forward.h
  cdhashset.h
  cdhashset_forward.h
  cdinsert_hashmap.h
  cdinsert_hashmap_forward.h
  cdlist.h
  cdlist_forward.h
  cdmaybe.h
  cdo.h
  cdqueue.h
  cdtrail_queue.h
  context.cpp
  context.h
  context_mm.cpp
  context_mm.h
)

add_library(cvc5context OBJECT ${LIBCONTEXT_SOURCES})
if(ENABLE_SHARED)
  set_target_properties(cvc5context PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()
target_compile_definitions(cvc5context PRIVATE -D__BUILDING_CVC5LIB)
