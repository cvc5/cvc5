###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Responsible to identify the version of this source tree, expose this version
# information to the rest of cmake and properly update the versioninfo.cpp. 
#
# Note that the above responsibilities are split among configure and build
# time. To achieve this, this file is both executed as a part of the regular
# cmake setup during configure time, but also adds a special target to call
# itself during build time to always keep versioninfo.cpp updated.
##

if(CMAKE_SCRIPT_MODE_FILE)
  # was run as standalone script
  set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
else()
  # was run within the overall cmake project
  # add target to update versioninfo.cpp at build time
  add_custom_target(gen-versioninfo
    COMMAND ${CMAKE_COMMAND}
      -DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
      -DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
      -P ${PROJECT_SOURCE_DIR}/cmake/version.cmake
  )
endif()

# include basic version information
include(version-base)

# now use git to retrieve additional version information
find_package(Git)
if(GIT_FOUND)
  # git is available

  # call git describe. If result is not 0 this is not a git repository
  execute_process(
      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} describe --long --tags --match cvc5-*
      RESULT_VARIABLE GIT_RESULT
      OUTPUT_VARIABLE GIT_DESCRIBE
      OUTPUT_STRIP_TRAILING_WHITESPACE
  )

  if(GIT_RESULT EQUAL 0)
    # it is a git working copy

    set(GIT_BUILD "true")
    # get current git branch
    execute_process(
        COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} rev-parse --abbrev-ref HEAD
        RESULT_VARIABLE GIT_RESULT
        OUTPUT_VARIABLE GIT_BRANCH
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    # result is != 0 if worktree is dirty
    # note: git diff HEAD shows both staged and unstaged changes.
    execute_process(
      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} diff HEAD --quiet
      RESULT_VARIABLE GIT_RESULT
    )
    if(GIT_RESULT EQUAL 0)
      set(GIT_DIRTY_MSG "")
    else()
      set(GIT_DIRTY_MSG " with local modifications")
    endif()

    string(REGEX MATCH "^cvc5-([0-9.]+)-([0-9]+)-g([0-9a-f]+)$" MATCH "${GIT_DESCRIBE}")
    if(NOT MATCH)
      message(SEND_ERROR "Unexpected format from 'git describe': '${GIT_DESCRIBE}'")
    endif()
    set(GIT_LAST_TAG "${CMAKE_MATCH_1}")
    set(GIT_COMMITS_SINCE_TAG "${CMAKE_MATCH_2}")
    set(GIT_COMMIT "${CMAKE_MATCH_3}")

    if(GIT_COMMITS_SINCE_TAG EQUAL "0")
      # this version *is* a tag
      set(CVC5_IS_RELEASE "true")
      set(CVC5_VERSION "${GIT_LAST_TAG}")
      set(CVC5_FULL_VERSION "${GIT_LAST_TAG}")
      set(CVC5_GIT_INFO "git tag ${GIT_LAST_TAG} branch ${GIT_BRANCH}${GIT_DIRTY_MSG}")
    else()
      # this version is not a tag

      # increment patch part of version
      string(REGEX MATCHALL "[0-9]+" VERSION_LIST "${GIT_LAST_TAG}")
      list(LENGTH VERSION_LIST VERSION_LIST_LENGTH)
      # append .0 until we have a patch part
      while(VERSION_LIST_LENGTH LESS "3")
        list(APPEND VERSION_LIST "0")
        list(LENGTH VERSION_LIST VERSION_LIST_LENGTH)
      endwhile()
      # increment patch part
      list(GET VERSION_LIST 2 VERSION_LAST_NUMBER)
      list(REMOVE_AT VERSION_LIST 2)
      math(EXPR VERSION_LAST_NUMBER "${VERSION_LAST_NUMBER} + 1")
      list(APPEND VERSION_LIST ${VERSION_LAST_NUMBER})
      # join version string into GIT_LAST_TAG
      list(GET VERSION_LIST 0 GIT_LAST_TAG)
      while(VERSION_LIST_LENGTH GREATER "1")
        list(REMOVE_AT VERSION_LIST 0)
        list(GET VERSION_LIST 0 TMP)
        set(GIT_LAST_TAG "${GIT_LAST_TAG}.${TMP}")
        list(LENGTH VERSION_LIST VERSION_LIST_LENGTH)
      endwhile()

      if(CVC5_IS_RELEASE)
        set(CVC5_VERSION "${CVC5_VERSION}-modified")
        set(CVC5_FULL_VERSION "${CVC5_FULL_VERSION}-modified")
      else()
        set(CVC5_VERSION "${GIT_LAST_TAG}-dev")
        set(CVC5_FULL_VERSION "${GIT_LAST_TAG}-dev.${GIT_COMMITS_SINCE_TAG}.${GIT_COMMIT}")
      endif()
      set(CVC5_GIT_INFO "git ${GIT_COMMIT} on branch ${GIT_BRANCH}${GIT_DIRTY_MSG}")
    endif()
  endif()
endif()

# actually configure versioninfo.cpp
configure_file(
    ${PROJECT_SOURCE_DIR}/src/base/versioninfo.cpp.in ${CMAKE_BINARY_DIR}/src/base/versioninfo.cpp)
