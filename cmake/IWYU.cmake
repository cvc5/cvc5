find_program(IWYU_PATH iwyu_tool)

if(IWYU_PATH)
    # iwyu is available

    # add a target to inspect number of times headers are included.
    add_custom_target(iwyu-list-includes
        COMMAND grep -hor "\"#include .*\""  ${PROJECT_SOURCE_DIR}/src | sort | uniq -c | sort -n
    )

    # find the standard library directory
    file(GLOB_RECURSE LLVM_INCLUDE /usr/lib*/llvm*/**/stddef.h)
    if(LLVM_INCLUDE)
        list(GET LLVM_INCLUDE 0 LLVM_INCLUDE)
        get_filename_component(LLVM_INCLUDE "${LLVM_INCLUDE}" DIRECTORY)
        set(LLVM_INCLUDE "-I${LLVM_INCLUDE}")
    endif()

    # add a target to run iwyu on all files (within the compilation database)
    add_custom_target(iwyu-all
        COMMAND ${IWYU_PATH} -o clang -p . -- -Xiwyu --cxx17ns ${LLVM_INCLUDE}
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
            COMMAND ${IWYU_PATH} -o clang -j4 -p . ${source_files} -- -Xiwyu --cxx17ns ${LLVM_INCLUDE}
        )
    endforeach()
endif()
