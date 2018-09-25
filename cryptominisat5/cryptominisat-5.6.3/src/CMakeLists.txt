# Copyright (c) 2017, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

include_directories(
    ${PROJECT_SOURCE_DIR}
)

if (NOT WIN32)
    add_cxx_flag_if_supported("-Wno-bitfield-constant-conversion")
    #add_cxx_flag_if_supported("-Wduplicated-cond")
    #add_cxx_flag_if_supported("-Wduplicated-branches")
    add_cxx_flag_if_supported("-Wlogical-op")
    add_cxx_flag_if_supported("-Wrestrict")
    add_cxx_flag_if_supported("-Wnull-dereference")
    add_cxx_flag_if_supported("-Wjump-misses-init")
    add_cxx_flag_if_supported("-Wdouble-promotion")
    add_cxx_flag_if_supported("-Wshadow")
    add_cxx_flag_if_supported("-Wformat=2")
    add_cxx_flag_if_supported("-Wextra-semi")
    add_cxx_flag_if_supported("-pedantic")
    add_cxx_flag_if_supported("-Wno-class-memaccess")
    #add_cxx_flag_if_supported("-Wdeprecated")
endif()
add_sanitize_flags()

include_directories(${CMAKE_CURRENT_BINARY_DIR})

if(Boost_FOUND)
    include_directories(${Boost_INCLUDE_DIRS})
endif()

if (ENABLE_TESTING)
    add_definitions( -DCMS_TESTING_ENABLED )
    set(GTEST_PREFIX ${PROJECT_SOURCE_DIR}/utils/gtest)
    include_directories(${GTEST_PREFIX}/include)
endif()

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/cryptominisat.h.in" "${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/cryptominisat.h" @ONLY)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/solvertypesmini.h.in" "${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/solvertypesmini.h" @ONLY)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/cryptominisat_c.h.in" "${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/cryptominisat_c.h" @ONLY)

if (SQLITE3_FOUND AND STATS)
    if (NOT PYTHON_EXECUTABLE)
        MESSAGE(FATAL_ERROR "Unfortunately, the python interpreter is needed for statistics because of SQL text generation")
    endif()

    add_custom_command(
        OUTPUT  ${CMAKE_CURRENT_BINARY_DIR}/sql_tablestructure.cpp
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMAND ${PYTHON_EXECUTABLE} ${CRYPTOMS_SCRIPTS_DIR}/xxd-alike.py cmsat_tablestructure.sql ${CMAKE_CURRENT_BINARY_DIR}/sql_tablestructure.cpp
        DEPENDS ${CMAKE_SOURCE_DIR}/cmsat_tablestructure.sql
    )
    add_custom_target(tablestruct ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/sql_tablestructure.cpp)
endif()

set(cryptoms_lib_files
    cnf.cpp
    propengine.cpp
    varreplacer.cpp
    clausecleaner.cpp
    clauseusagestats.cpp
    prober.cpp
    occsimplifier.cpp
    subsumestrengthen.cpp
    clauseallocator.cpp
    sccfinder.cpp
    solverconf.cpp
    distillerlong.cpp
    distillerlongwithimpl.cpp
    str_impl_w_impl_stamp.cpp
    solutionextender.cpp
    completedetachreattacher.cpp
    searcher.cpp
    solver.cpp
    sqlstats.cpp
    implcache.cpp
    stamp.cpp
    compfinder.cpp
    comphandler.cpp
    hyperengine.cpp
    subsumeimplicit.cpp
    datasync.cpp
    reducedb.cpp
    clausedumper.cpp
    bva.cpp
    intree.cpp
    features_calc.cpp
    features_to_reconf.cpp
    solvefeatures.cpp
    searchstats.cpp
    xorfinder.cpp
    cryptominisat_c.cpp
#    watcharray.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)

set(cryptoms_lib_link_libs "")

if (USE_GAUSS)
    SET(cryptoms_lib_files ${cryptoms_lib_files}
        EGaussian.cpp
        packedrow.cpp
        matrixfinder.cpp
    )
endif()

if (M4RI_FOUND)
    include_directories(${M4RI_INCLUDE_DIRS})

    SET(cryptoms_lib_files ${cryptoms_lib_files} toplevelgauss.cpp)
    SET(cryptoms_lib_link_libs ${cryptoms_lib_link_libs} ${M4RI_LIBRARIES})
endif (M4RI_FOUND)

if (SQLITE3_FOUND AND STATS)
    SET(cryptoms_lib_files ${cryptoms_lib_files}
        sqlitestats.cpp
        ${CMAKE_CURRENT_BINARY_DIR}/sql_tablestructure.cpp
    )
    SET(cryptoms_lib_link_libs ${cryptoms_lib_link_libs} ${SQLITE3_LIBRARIES})
endif ()

if (NOT STATICCOMPILE)
    add_library(libcryptominisat5 SHARED
        ${cryptoms_lib_files}
        cryptominisat.cpp
    )
else()
    add_library(libcryptominisat5 STATIC
        ${cryptoms_lib_files}
        cryptominisat.cpp
    )
endif()
GENERATE_EXPORT_HEADER(libcryptominisat5
         BASE_NAME libcryptominisat5
         #EXPORT_MACRO_NAME libcryptominisat5_EXPORT
         #EXPORT_FILE_NAME MyLibrary_Export.h
         #STATIC_DEFINE MyLibrary_BUILT_AS_STATIC
)

if (SQLITE3_FOUND AND STATS)
    add_dependencies(libcryptominisat5
        tablestruct
    )
endif()

# indicate that we depend on pthread, and compile in the actual library
target_link_libraries(libcryptominisat5
    LINK_PUBLIC ${cryptoms_lib_link_libs}
    LINK_PUBLIC ${CMAKE_THREAD_LIBS_INIT}
)

if (NOT WIN32)
    set_target_properties(libcryptominisat5 PROPERTIES
        OUTPUT_NAME cryptominisat5
        PUBLIC_HEADER "${cryptominisat5_public_headers}"
        VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
        SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    )
else()
    set_target_properties(libcryptominisat5 PROPERTIES
        OUTPUT_NAME cryptominisat5win
        PUBLIC_HEADER "${cryptominisat5_public_headers}"
        VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
        SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    )
endif()

if (IPASIR)
    if (NOT STATICCOMPILE)
        add_library(ipasircryptominisat5 SHARED
            ipasir.cpp
        )
    else()
        add_library(ipasircryptominisat5 STATIC
            ipasir.cpp
        )
    endif()
    target_link_libraries(ipasircryptominisat5
        LINK_PUBLIC ${cryptoms_lib_link_libs} libcryptominisat5
    )
    set_target_properties(ipasircryptominisat5 PROPERTIES
        OUTPUT_NAME ipasircryptominisat5
        PUBLIC_HEADER "${cryptominisat5_public_headers}"
        VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
        SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    )
    install(TARGETS ipasircryptominisat5
        EXPORT ${CRYPTOMINISAT5_EXPORT_NAME}
        LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
        PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/cryptominisat5"
    )

endif()

cmsat_add_public_header(libcryptominisat5 ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/cryptominisat_c.h )
cmsat_add_public_header(libcryptominisat5 ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/cryptominisat.h )
cmsat_add_public_header(libcryptominisat5 ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat5/solvertypesmini.h )
cmsat_add_public_header(libcryptominisat5 ${CMAKE_CURRENT_SOURCE_DIR}/dimacsparser.h )
cmsat_add_public_header(libcryptominisat5 ${CMAKE_CURRENT_SOURCE_DIR}/streambuffer.h )

# -----------------------------------------------------------------------------
# Copy public headers into build directory include directory.
# The cryptominisat5Config.cmake we generate in the build directory depends on
# this.
# -----------------------------------------------------------------------------
set(HEADER_DEST "${PROJECT_BINARY_DIR}/include/cryptominisat5")
add_custom_target(CopyPublicHeaders ALL)
get_target_property(cryptominisat5_public_headers libcryptominisat5 PUBLIC_HEADER)
foreach(public_header ${cryptominisat5_public_headers})
    get_filename_component(HEADER_NAME ${public_header} NAME)
    add_custom_command(TARGET CopyPublicHeaders PRE_BUILD
                       COMMAND ${CMAKE_COMMAND} -E make_directory
                               "${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E echo
                       "Copying ${HEADER_NAME} to ${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E
                           copy_if_different
                           ${public_header}
                           "${HEADER_DEST}"
                      )
endforeach()

install(TARGETS libcryptominisat5
    EXPORT ${CRYPTOMINISAT5_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/cryptominisat5"
)

if (NOT ONLY_SIMPLE)
    add_executable(cryptominisat5
        main.cpp
        main_exe.cpp
        signalcode.cpp
    )
endif()

if (EMSCIPTEN)
add_executable(cryptominisat5_simple
    main_emscripten.cpp
)

set_target_properties(
  cryptominisat5_simple PROPERTIES LINK_FLAGS "-s WASM=1 -s ALLOW_MEMORY_GROWTH=1 -s EXTRA_EXPORTED_RUNTIME_METHODS='[\"ccall\", \"cwrap\"]'  -s LINKABLE=1 -s EXPORT_ALL=1"
)

SET_SOURCE_FILES_PROPERTIES(main_emscripten.cpp
    PROPERTIES COMPILE_FLAGS "-s WASM=1 -s ALLOW_MEMORY_GROWTH=1 -s EXTRA_EXPORTED_RUNTIME_METHODS='[\"ccall\", \"cwrap\"]'  -s LINKABLE=1 -s EXPORT_ALL=1"
)

else()
add_executable(cryptominisat5_simple
    main_simple.cpp
)
endif()

set(cryptoms_exec_link_libs
    libcryptominisat5
)

IF (ZLIB_FOUND)
    SET(cryptoms_exec_link_libs ${cryptoms_exec_link_libs} ${ZLIB_LIBRARY})
ENDIF()

if (STATICCOMPILE)
    SET_TARGET_PROPERTIES(cryptominisat5_simple PROPERTIES LINK_SEARCH_START_STATIC 1)
endif()
set_target_properties(cryptominisat5_simple PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
    INSTALL_RPATH_USE_LINK_PATH TRUE)
if (STATICCOMPILE)
    SET_TARGET_PROPERTIES(cryptominisat5_simple PROPERTIES LINK_SEARCH_END_STATIC 1)
endif()
target_link_libraries(cryptominisat5_simple
    ${cryptoms_exec_link_libs}
)
install(TARGETS cryptominisat5_simple
    EXPORT ${CRYPTOMINISAT5_EXPORT_NAME}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
SET(CPACK_PACKAGE_EXECUTABLES "cryptominisat5_simple")

if (NOT ONLY_SIMPLE)
    if (STATICCOMPILE)
        SET_TARGET_PROPERTIES(cryptominisat5 PROPERTIES LINK_SEARCH_START_STATIC 1)
    endif()
    set_target_properties(cryptominisat5 PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
        INSTALL_RPATH_USE_LINK_PATH TRUE)
    if (STATICCOMPILE)
        SET_TARGET_PROPERTIES(cryptominisat5 PROPERTIES LINK_SEARCH_END_STATIC 1)
    endif()
    target_link_libraries(cryptominisat5
        ${cryptoms_exec_link_libs}
        ${Boost_LIBRARIES}
    )
    install(TARGETS cryptominisat5
        EXPORT ${CRYPTOMINISAT5_EXPORT_NAME}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
    )
    SET(CPACK_PACKAGE_EXECUTABLES "cryptominisat5")
endif()


if (FEEDBACKFUZZ)
    add_executable(cms_feedback_fuzz
        fuzz.cpp
        libfuzz/FuzzerCrossOver.cpp
        libfuzz/FuzzerDriver.cpp
        libfuzz/FuzzerInterface.cpp
        libfuzz/FuzzerIO.cpp
        libfuzz/FuzzerLoop.cpp
        libfuzz/FuzzerMain.cpp
        libfuzz/FuzzerMutate.cpp
        libfuzz/FuzzerSanitizerOptions.cpp
        libfuzz/FuzzerSHA1.cpp
        libfuzz/FuzzerTraceState.cpp
        libfuzz/FuzzerUtil.cpp
    )
    target_link_libraries(cms_feedback_fuzz
        ${cryptoms_exec_link_libs}
    )

    set_target_properties(cms_feedback_fuzz PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
endif()
