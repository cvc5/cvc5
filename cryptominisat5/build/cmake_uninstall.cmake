cmake_policy(SET CMP0007 NEW) # Suppress warnings see `cmake --help-policy CMP0007`

if (NOT EXISTS "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/install_manifest.txt")
    message(FATAL_ERROR "Cannot find install manifest: \"/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/install_manifest.txt\"")
endif(NOT EXISTS "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/install_manifest.txt")

file(READ "/Users/anwu/Monkeyswedding/Projects/cvc4Preprocess/CVC4/cryptominisat5/build/install_manifest.txt" files)
string(REGEX REPLACE "\n" ";" files "${files}")
list(REVERSE files)
foreach (file ${files})
    message(STATUS "Uninstalling \"$ENV{DESTDIR}${file}\"")
    if (EXISTS "$ENV{DESTDIR}${file}")
        execute_process(
            COMMAND /usr/local/Cellar/cmake/3.12.2/bin/cmake -E remove "$ENV{DESTDIR}${file}"
            OUTPUT_VARIABLE rm_out
            RESULT_VARIABLE rm_retval
        )
        if(NOT ${rm_retval} EQUAL 0)
            message(FATAL_ERROR "Problem when removing \"$ENV{DESTDIR}${file}\"")
        endif (NOT ${rm_retval} EQUAL 0)
    else (EXISTS "$ENV{DESTDIR}${file}")
        message(STATUS "File \"$ENV{DESTDIR}${file}\" does not exist.")
    endif (EXISTS "$ENV{DESTDIR}${file}")
endforeach(file)
