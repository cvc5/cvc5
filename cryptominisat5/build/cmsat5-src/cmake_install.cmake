# Install script for directory: /Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/cryptominisat-5.6.3/src

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/install")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "RelWithDebInfo")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/lib/libcryptominisat5.a")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libcryptominisat5.a" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libcryptominisat5.a")
    execute_process(COMMAND "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/ranlib" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/libcryptominisat5.a")
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/cryptominisat5" TYPE FILE FILES
    "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/cmsat5-src/cryptominisat5/cryptominisat_c.h"
    "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/cmsat5-src/cryptominisat5/cryptominisat.h"
    "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/cmsat5-src/cryptominisat5/solvertypesmini.h"
    "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/cryptominisat-5.6.3/src/dimacsparser.h"
    "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/cryptominisat-5.6.3/src/streambuffer.h"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE EXECUTABLE FILES "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/cryptominisat5_simple")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/cryptominisat5_simple" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/cryptominisat5_simple")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/cryptominisat5_simple")
    endif()
  endif()
endif()

