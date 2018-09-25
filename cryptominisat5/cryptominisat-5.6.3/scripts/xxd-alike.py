#!/usr/bin/env python

# Copyright (c) 2017, Martin Horenovsky
# Copyright (c) 2018, Mate Soos

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

import sys

PY3 = sys.version_info.major == 3

input_name = sys.argv[1]
output_path = sys.argv[2]
output_name = input_name.replace('.', '_')


# In python 3, opening file as rb will return bytes and iteration is per byte
# In python 2, opening file as rb will return string and iteration is per char
# and char need to be converted to bytes.
# This function papers over the differences
def convert(c):
    if PY3:
        return c
    return ord(c)


with open(input_name, 'rb') as file:
    contents = file.read()


with open(output_path, 'w') as out:
    out.write('unsigned char {}[] = {{'.format(output_name))
    first = True
    for i, byte in enumerate(contents):
        if not first:
            out.write(', ')
        first = False
        if i % 12 == 0:
            out.write('\n  ')
        out.write('0x{:02x}'.format(convert(byte)))

    out.write(', 0x00')
    out.write('\n};\n')

    out.write('unsigned int {}_len = {};\n'.format(output_name, len(contents)))
