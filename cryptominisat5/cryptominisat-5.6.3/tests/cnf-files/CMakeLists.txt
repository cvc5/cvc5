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

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg.in2 @ONLY)

if (MSVC)
    file(GENERATE
         OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>/lit.site.cfg
         INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.in2)


    # Make sure this test-suite runs when "test" is target
    add_test(NAME CNF
            COMMAND ${LIT_TOOL} ${LIT_ARGS} .
            WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>/"
    )
else()
    file(GENERATE
         OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
         INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.in2)


    # Make sure this test-suite runs when "test" is target
    add_test(NAME CNF
            COMMAND ${LIT_TOOL} ${LIT_ARGS} .
            WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
endif()

