find_program(IWYU_PATH NAMES iwyu_tool iwyu-tool)

if(IWYU_PATH)
    # iwyu is available
    message(STATUS "Found IWYU: ${IWYU_PATH}")

    # add a target to inspect number of times headers are included.
    add_custom_target(iwyu-list-includes
        COMMAND grep -hor "\"#include .*\""  ${PROJECT_SOURCE_DIR}/src | sort | uniq -c | sort -n
    )

    # find the standard library directory
    find_program(CLANG_PATH clang REQUIRED)
    execute_process(COMMAND ${CLANG_PATH} -print-resource-dir
        OUTPUT_VARIABLE LLVM_INCLUDE_DIR
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if(LLVM_INCLUDE_DIR)
        set(LLVM_INCLUDE_DIR "-I${LLVM_INCLUDE_DIR}/include")
    endif()

    # add a target to run iwyu on all files (within the compilation database)
    add_custom_target(iwyu-all
        COMMAND ${IWYU_PATH} -o clang -p . -- -Xiwyu --cxx17ns ${LLVM_INCLUDE_DIR}
    )

    file(GLOB subdirs ${PROJECT_SOURCE_DIR}/src/*)
    foreach(dir ${subdirs})
        # add a target for every subdirectory
        file(GLOB_RECURSE source_files
            ${dir}/*.cpp
            ${dir}/*.cc
        )
        get_filename_component(dirname ${dir} NAME)
        add_custom_target(iwyu-${dirname}
            COMMAND ${IWYU_PATH} -o clang -p . ${source_files} -- -Xiwyu --cxx17ns ${LLVM_INCLUDE_DIR}
        )
    endforeach()
endif()
