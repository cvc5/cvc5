###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Alex Ozdemir, Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find cvc5 pythonic api.
# CVC5PythonicAPI_FOUND - found cvc5 pythonic api
# CVC5PythonicAPI_BASEDIR - the base directory of the cvc5 pythonic api
##

include(deps-helper)


include(ExternalProject)
if(PYTHONIC_PATH)
  ExternalProject_Add(
    CVC5PythonicAPI
    ${COMMON_EP_CONFIG}
    SOURCE_DIR ${PYTHONIC_PATH}
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
  )
else()
  check_ep_downloaded("CVC5PythonicAPI")
  if(NOT CVC5PythonicAPI_DOWNLOADED)
    check_auto_download("CVC5PythonicAPI" "--no-python-bindings")
  endif()

  set(CVC5PythonicAPI_VERSION "cdcac7cb2da79d922fc44628c1c3c5f60c2eeec4")
  ExternalProject_Add(
    CVC5PythonicAPI
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/cvc5_pythonic_api/archive/${CVC5PythonicAPI_VERSION}.zip
    URL_HASH SHA256=85630465037f1cd864452d3999dd4e2a2f074822a8a310f1179d672dc8d24d16
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
  )
endif()

set(CVC5PythonicAPI_FOUND TRUE)
ExternalProject_Get_Property(CVC5PythonicAPI SOURCE_DIR)
set(CVC5PythonicAPI_BASEDIR "${SOURCE_DIR}")

mark_as_advanced(CVC5PythonicAPI_FOUND)
mark_as_advanced(CVC5PythonicAPI_BASEDIR)
message(STATUS "Pythonic API: ${CVC5PythonicAPI_BASEDIR}")
