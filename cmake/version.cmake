###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

if(CMAKE_SCRIPT_MODE_FILE)
  set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
else()
  add_custom_target(gen-versioninfo
    BYPRODUCTS
      ${CMAKE_BINARY_DIR}/src/base/versioninfo.cpp
    COMMAND ${CMAKE_COMMAND}
      -DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
      -DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
      -P ${PROJECT_SOURCE_DIR}/cmake/version.cmake)
endif()

include(version-base)

find_package(Git)
if(GIT_FOUND)
  # git is available

  # Get git describe, result is != 0 if this is not a git repository
  execute_process(
      COMMAND ${GIT_EXECUTABLE} describe --long --tags --match cvc5-*
      RESULT_VARIABLE GIT_RESULT
      OUTPUT_VARIABLE GIT_DESCRIBE
      OUTPUT_STRIP_TRAILING_WHITESPACE
  )

  if(GIT_RESULT EQUAL 0)
    # it is a git working copy

    set(GIT_BUILD "true")
    # Get current git branch
    execute_process(
        COMMAND ${GIT_EXECUTABLE} rev-parse --abbrev-ref HEAD
        RESULT_VARIABLE GIT_RESULT
        OUTPUT_VARIABLE GIT_BRANCH
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    # Result is != 0 if worktree is dirty
    # Note: git diff HEAD shows both staged and unstaged changes.
    execute_process(
      COMMAND ${GIT_EXECUTABLE} diff HEAD --quiet
      RESULT_VARIABLE GIT_RESULT
    )
    if(GIT_RESULT EQUAL 0)
      set(GIT_DIRTY_MSG "")
    else()
      set(GIT_DIRTY_MSG " with local modifications")
    endif()

    if(GIT_DESCRIBE MATCHES "^.*-0-g[0-9a-f]+$")
      # this version *is* a tag
      set(CVC5_IS_RELEASE "true")
      string(REGEX REPLACE "^(.*)-0-g[0-9a-f]+$" "\\1" GIT_LAST_TAG "${GIT_DESCRIBE}")
      set(CVC5_VERSION "${GIT_LAST_TAG}")
      set(CVC5_FULL_VERSION "${GIT_LAST_TAG}")
      set(CVC5_GIT_INFO "git tag ${GIT_LAST_TAG} branch ${GIT_BRANCH}${GIT_DIRTY_MSG}")
    elseif(GIT_DESCRIBE MATCHES "^.*-[0-9]+-g[0-9a-f]+$")
      # this version is not a tag
      string(REGEX REPLACE "^(.*)-[0-9]+-g[0-9a-f]+$" "\\1" GIT_LAST_TAG "${GIT_DESCRIBE}")
      string(REGEX REPLACE "^.*-([0-9]+)-g[0-9a-f]+$" "\\1" GIT_COMMITS_SINCE_TAG "${GIT_DESCRIBE}")
      string(REGEX REPLACE "^.*-g([0-9a-f]+)$" "\\1" GIT_COMMIT "${GIT_DESCRIBE}")
      set(CVC5_VERSION "${GIT_LAST_TAG}-dev")
      set(CVC5_FULL_VERSION "${GIT_LAST_TAG}-dev.${GIT_COMMITS_SINCE_TAG}.${GIT_COMMIT}")
      set(CVC5_GIT_INFO "git ${GIT_COMMIT} on branch ${GIT_BRANCH}${GIT_DIRTY_MSG}")
    else()
      message(SEND_ERROR "Unexpected format from 'git describe': '${GIT_DESCRIBE}'")
    endif()
  endif()
endif()

configure_file(
    ${PROJECT_SOURCE_DIR}/src/base/versioninfo.cpp.in ${CMAKE_BINARY_DIR}/src/base/versioninfo.cpp)
